module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalQ8

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns

section General

variable {X : Type*} [Group X]

theorem l3b_card_comap [Finite X] (N : Subgroup X) [N.Normal] (F : Subgroup (X ⧸ N)) :
    Nat.card (F.comap (QuotientGroup.mk' N)) = Nat.card F * Nat.card N := by
  have h1 : Nat.card X = Nat.card (X ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have h2 : Nat.card F * F.index = Nat.card (X ⧸ N) := Subgroup.card_mul_index F
  have h3 : Nat.card (F.comap (QuotientGroup.mk' N)) * (F.comap (QuotientGroup.mk' N)).index =
      Nat.card X := Subgroup.card_mul_index _
  have h4 : (F.comap (QuotientGroup.mk' N)).index = F.index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)
  have h5 : F.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [h4] at h3
  have : Nat.card (F.comap (QuotientGroup.mk' N)) * F.index = (Nat.card F * Nat.card N) * F.index := by
    rw [h3, h1, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h5) this

theorem l3b_c_move {c : X} (hc : ∀ g, g * c = c * g) (u v : X) : u * c * v = u * v * c := by
  rw [mul_assoc, ← hc v, ← mul_assoc]

theorem l3b_cube_mul {a b c : X} (hc : ∀ g, g * c = c * g) (hab : b * a = a * b * c)
    (hc3 : c ^ 3 = 1) : (a * b) ^ 3 = a ^ 3 * b ^ 3 := by
  have h3 : (a * b) ^ 3 = a * (b * a) * (b * a) * b := by rw [pow_three']; group
  have hccc : c * c * c = 1 := by rw [← pow_three', hc3]
  rw [h3, hab, pow_three' a, pow_three' b]
  calc a * (a * b * c) * (a * b * c) * b = (a * a * b) * c * (a * b) * c * b := by group
    _ = (a * a * b) * (a * b) * c * c * b := by rw [l3b_c_move hc (a * a * b) (a * b)]
    _ = a * a * (b * a) * b * c * c * b := by group
    _ = a * a * (a * b * c) * b * c * c * b := by rw [hab]
    _ = (a * a * a * b) * c * b * c * c * b := by group
    _ = (a * a * a * b) * b * c * c * c * b := by rw [l3b_c_move hc (a * a * a * b) b]
    _ = a * a * a * b * b * (c * c * c) * b := by group
    _ = a * a * a * (b * b * b) := by rw [hccc]; group

theorem l3b_fused_of_q8 [Finite X] {F : Subgroup X} (hF : IsElemAbelian 3 F)
    (hc : Nat.card F = 9) (h : AutHasQ8 F) : TotallyFused F := by
  intro f hf hf1 f' hf' hf1'
  obtain ⟨g, -, hg⟩ := l3b_q8_transitive (J := ⊤) hF hc h f hf f' hf' hf1 hf1'
  exact ⟨g, hg⟩

theorem l3b_not_fused_of_cube [Finite X] (hZ3 : ∀ z ∈ Subgroup.center X, z ^ 3 = 1)
    (hZc : Nat.card (Subgroup.center X) = 3) {F : Subgroup (X ⧸ Subgroup.center X)}
    (hF : IsElemAbelian 3 F) (hc : Nat.card F = 9)
    (hnot : ∃ x ∈ F.comap (QuotientGroup.mk' (Subgroup.center X)), x ^ 3 ≠ 1) :
    ¬ TotallyFused F := by
  set Z := Subgroup.center X with hZ
  set Fh := F.comap (QuotientGroup.mk' Z) with hFh
  have hFhc : Nat.card Fh = 27 := by rw [hFh, l3b_card_comap, hc, hZc]
  have hmem : ∀ x : X, x ∈ Fh ↔ (QuotientGroup.mk x : X ⧸ Z) ∈ F := fun x => Iff.rfl
  have hcub : ∀ x ∈ Fh, x ^ 3 ∈ Z := by
    intro x hx
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hF.2 _ ((hmem x).1 hx)
  have hcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, ∃ c ∈ Z, y * x = x * y * c := by
    intro x hx y hy
    refine ⟨(x * y)⁻¹ * (y * x), ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul]
    have := congrArg Subtype.val (hF.1.is_comm.comm ⟨_, (hmem x).1 hx⟩ ⟨_, (hmem y).1 hy⟩)
    simp only [Subgroup.coe_mul] at this
    rw [this, inv_mul_cancel]
  let κ : ↥Fh →* ↥Z :=
    { toFun := fun x => ⟨(x : X) ^ 3, hcub x x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        obtain ⟨c, hcZ, hc'⟩ := hcomm x x.2 y y.2
        apply Subtype.ext
        change ((x : X) * y) ^ 3 = (x : X) ^ 3 * (y : X) ^ 3
        exact l3b_cube_mul (fun g => (Subgroup.mem_center_iff.1 hcZ g)) hc' (hZ3 c hcZ) }
  have hker := Subgroup.card_ker_mul_card_range κ
  have hrange : Nat.card κ.range ≤ 3 := by
    rw [← hZc]
    exact Subgroup.card_le_of_le (le_top : κ.range ≤ ⊤) |>.trans (by simp)
  have hkerc : 9 ≤ Nat.card κ.ker := by
    rw [hFhc] at hker
    by_contra hlt
    push Not at hlt
    have : Nat.card κ.ker * Nat.card κ.range ≤ 8 * 3 :=
      Nat.mul_le_mul (by omega) hrange
    omega
  obtain ⟨u, huF, hu3, huZ⟩ : ∃ u ∈ Fh, u ^ 3 = 1 ∧ u ∉ Z := by
    by_contra hall
    push Not at hall
    have hle : (κ.ker.map Fh.subtype) ≤ Z := by
      rintro _ ⟨t, ht, rfl⟩
      by_contra hn
      have h1 := hall t t.2
      have : (t : X) ^ 3 = 1 := by
        have := (MonoidHom.mem_ker.1 ht)
        exact congrArg Subtype.val this
      exact hn (by simpa using h1 this)
    have h2 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective Fh.subtype_injective, hZc] at h2
    omega
  obtain ⟨w, hwFh, hw3⟩ := hnot
  intro hfused
  have hwZ : w ∉ Z := fun h => hw3 (hZ3 w h)
  have hu1 : (QuotientGroup.mk u : X ⧸ Z) ≠ 1 := fun h => huZ ((QuotientGroup.eq_one_iff u).1 h)
  have hw1 : (QuotientGroup.mk w : X ⧸ Z) ≠ 1 := fun h => hwZ ((QuotientGroup.eq_one_iff w).1 h)
  obtain ⟨k, hk⟩ := hfused _ ((hmem u).1 huF) hu1 _ ((hmem w).1 hwFh) hw1
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective k
  have hk' : (QuotientGroup.mk (k' * u * k'⁻¹) : X ⧸ Z) = QuotientGroup.mk w := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]; exact hk
  rw [QuotientGroup.eq] at hk'
  set z := (k' * u * k'⁻¹)⁻¹ * w with hzdef
  have hw : w = (k' * u * k'⁻¹) * z := by rw [hzdef]; group
  have hzc : Commute (k' * u * k'⁻¹) z := (Subgroup.mem_center_iff.1 hk' _)
  apply hw3
  rw [hw, hzc.mul_pow, hZ3 z hk']
  have : (k' * u * k'⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hu3]; group
  rw [this, one_mul]

theorem l3b_nil_core {H H' : Type*} [Group H] [Finite H] [Group H'] (A : Subgroup H) [A.Normal]
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hidx : A.index = 3) (π : H →* H')
    (hπ : Function.Surjective π) : IsThreeNilpotent H' := by
  classical
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  set k := (Nat.card A).factorization 3 with hk
  set m := Nat.card A / 3 ^ k with hm
  have hmcop : Nat.Coprime 3 m := Nat.coprime_ordCompl Nat.prime_three hA0
  have hkm : 3 ^ k * m = Nat.card A := Nat.ordProj_mul_ordCompl_eq_self _ _
  let N3 : Subgroup H :=
    { carrier := {a | a ∈ A ∧ a ^ m = 1}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨A.mul_mem ha.1 hb.1, ?_⟩
        have hc : Commute a b := hcomm a ha.1 b hb.1
        rw [hc.mul_pow, ha.2, hb.2, one_mul]
      one_mem' := ⟨A.one_mem, one_pow _⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hmemN3 : ∀ a, a ∈ N3 ↔ a ∈ A ∧ a ^ m = 1 := fun a => Iff.rfl
  have h1 : ∀ a ∈ A, a ^ (3 ^ k) ∈ N3 := by
    intro a ha
    refine ⟨A.pow_mem ha _, ?_⟩
    have : (⟨a, ha⟩ : ↥A) ^ Nat.card A = 1 := pow_card_eq_one'
    have h' : a ^ Nat.card A = 1 := congrArg Subtype.val this
    rw [← pow_mul, hkm, h']
  have h2 : ∀ (u : H), ∀ a ∈ N3, u * a * u⁻¹ ∈ N3 := by
    intro u a ha
    refine ⟨Subgroup.Normal.conj_mem inferInstance a ha.1 u, ?_⟩
    rw [conj_pow, ha.2]; group
  have h3 : ¬ 3 ∣ Nat.card N3 := by
    intro h
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := N3) 3 h
    have : a ^ m = 1 := Subtype.ext a.2.2
    have h4 : 3 ∣ m := ha ▸ orderOf_dvd_of_pow_eq_one this
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hmcop h4
  have hN3n : N3.Normal := ⟨fun a ha u => h2 u a ha⟩
  have hN3m : (N3.map π).Normal := Subgroup.Normal.map hN3n π hπ
  refine ⟨N3.map π, hN3m, ?_, ?_⟩
  · refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => h3 (h.trans ?_)
    exact Subgroup.card_map_dvd N3 π
  · intro g
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨u, rfl⟩ := hπ t
    refine ⟨k + 1, ?_⟩
    rw [← QuotientGroup.mk_pow, ← map_pow, QuotientGroup.eq_one_iff]
    refine ⟨u ^ (3 ^ (k + 1)), ?_, rfl⟩
    have hu3 : u ^ 3 ∈ A := by
      have := Subgroup.pow_index_mem A u
      rwa [hidx] at this
    rw [pow_succ', pow_mul]
    exact h1 _ hu3

theorem l3b_threeNilpotent [Finite X] (x : X)
    (hA : ∀ a ∈ Subgroup.centralizer ({x} : Set X), ∀ b ∈ Subgroup.centralizer ({x} : Set X),
      a * b = b * a)
    (hidx : (Subgroup.centralizer ({x} : Set X)).relIndex
      ((Subgroup.centralizer ({(QuotientGroup.mk x : X ⧸ Subgroup.center X)} :
        Set (X ⧸ Subgroup.center X))).comap (QuotientGroup.mk' (Subgroup.center X))) = 3) :
    IsThreeNilpotent ↥(Subgroup.centralizer ({(QuotientGroup.mk x : X ⧸ Subgroup.center X)} :
      Set (X ⧸ Subgroup.center X))) := by
  set Z := Subgroup.center X with hZ
  set A := Subgroup.centralizer ({x} : Set X) with hAdef
  set Ck := Subgroup.centralizer ({(QuotientGroup.mk x : X ⧸ Z)} : Set (X ⧸ Z)) with hCk
  set C := Ck.comap (QuotientGroup.mk' Z) with hC
  have hCmem : ∀ u : X, u ∈ C ↔ (QuotientGroup.mk u : X ⧸ Z) * QuotientGroup.mk x =
      QuotientGroup.mk x * QuotientGroup.mk u := by
    intro u
    rw [hC, Subgroup.mem_comap, hCk, Subgroup.mem_centralizer_singleton_iff]
    exact Iff.rfl
  have hAmem : ∀ a : X, a ∈ A ↔ a * x = x * a := by
    intro a
    rw [hAdef, Subgroup.mem_centralizer_singleton_iff]
  have hAC : A ≤ C := by
    intro a ha
    rw [hCmem, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (hAmem a).1 ha]
  have hconj : ∀ u ∈ C, ∃ z ∈ Z, u * x * u⁻¹ = x * z := by
    intro u hu
    have h := (hCmem u).1 hu
    refine ⟨x⁻¹ * (u * x * u⁻¹), ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h]; group
  have hAn : ∀ u ∈ C, ∀ a ∈ A, u * a * u⁻¹ ∈ A := by
    intro u hu a ha
    obtain ⟨z, hz, hzu⟩ := hconj u hu
    rw [hAmem] at ha ⊢
    have hzc : ∀ g, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
    have hux : u⁻¹ * x * u = x * z⁻¹ := by
      have : x = (u⁻¹ * x * u) * z := by
        calc x = u⁻¹ * (u * x * u⁻¹) * u := by group
          _ = u⁻¹ * (x * z) * u := by rw [hzu]
          _ = u⁻¹ * x * (z * u) := by group
          _ = u⁻¹ * x * (u * z) := by rw [← hzc u]
          _ = (u⁻¹ * x * u) * z := by group
      calc u⁻¹ * x * u = (u⁻¹ * x * u) * z * z⁻¹ := by group
        _ = x * z⁻¹ := by rw [← this]
    have hax : a * x = x * a := ha
    have hzi : ∀ g, g * z⁻¹ = z⁻¹ * g := fun g => Subgroup.mem_center_iff.1 (inv_mem hz) g
    calc u * a * u⁻¹ * x = u * a * (u⁻¹ * x * u) * u⁻¹ := by group
      _ = u * a * (x * z⁻¹) * u⁻¹ := by rw [hux]
      _ = u * (a * x) * z⁻¹ * u⁻¹ := by group
      _ = u * (x * a) * z⁻¹ * u⁻¹ := by rw [hax]
      _ = (u * x * u⁻¹) * (u * a * z⁻¹ * u⁻¹) := by group
      _ = x * z * (u * a * z⁻¹ * u⁻¹) := by rw [hzu]
      _ = x * z * (u * a * u⁻¹ * z⁻¹) := by rw [l3b_c_move hzi (u * a) u⁻¹]
      _ = x * (z * (u * a * u⁻¹)) * z⁻¹ := by group
      _ = x * ((u * a * u⁻¹) * z) * z⁻¹ := by rw [← hzc (u * a * u⁻¹)]
      _ = x * (u * a * u⁻¹) := by group
  have hAnorm : (A.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hAn g g.2 n hn⟩
  have hcomm' : ∀ a ∈ A.subgroupOf C, ∀ b ∈ A.subgroupOf C, a * b = b * a :=
    fun a ha b hb => Subtype.ext (hA a ha b hb)
  have hidx' : (A.subgroupOf C).index = 3 := hidx
  let π : ↥C →* ↥Ck := ((QuotientGroup.mk' Z).comp C.subtype).codRestrict Ck (fun u => u.2)
  have hπ : Function.Surjective π := by
    intro t
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (t : X ⧸ Z)
    refine ⟨⟨u, ?_⟩, Subtype.ext hu⟩
    show QuotientGroup.mk' Z u ∈ Ck
    have : QuotientGroup.mk' Z u = (t : X ⧸ Z) := hu
    rw [this]; exact t.2
  exact l3b_nil_core (A.subgroupOf C) hcomm' hidx' π hπ

end General

end CFSG.HardMathSupport.Solomon.Coordinator
