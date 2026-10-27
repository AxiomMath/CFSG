module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Main
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Quasithin.Background.B2FactorizationBaumannAux
import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingPlaneCore
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.RankThree.PartTwo.KFacts.KP2

variable {G : Type} [Group G] [Finite G]

theorem a7r_exists_transvection {R : Subgroup G} (hR : IsElemAbelian 2 R) {a : G}
    (ha : a ∈ normalizer (R : Set G))
    (hca : Nat.card R < 4 * Nat.card (R ⊓ centralizer ({a} : Set G) : Subgroup G)) :
    ∃ β ∈ R, ∀ x ∈ R, a * x * a⁻¹ * x⁻¹ = 1 ∨ a * x * a⁻¹ * x⁻¹ = β := by
  set C : Subgroup G := R ⊓ centralizer ({a} : Set G)
  have hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hR.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hidx : C.relIndex R * Nat.card C = Nat.card R := by
    have := Subgroup.relIndex_mul_card C R
    rwa [inf_eq_left.mpr (inf_le_left : C ≤ R)] at this
  have hlt : C.relIndex R < 4 := by
    have hpos : 0 < Nat.card C := Nat.card_pos
    by_contra h
    have := Nat.mul_le_mul_right (Nat.card C) (not_lt.mp h)
    omega
  have hRp : IsPGroup 2 R := fun x => ⟨1, Subtype.ext (by simpa using hR.2 x x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hRp
  have hdvd : C.relIndex R ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card C R
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm2 : m < 2 := by
    by_contra h
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp h)
    omega
  interval_cases m
  ·
    refine ⟨1, R.one_mem, fun x hx => Or.inl ?_⟩
    have hxC : x ∈ C := (Subgroup.relIndex_eq_one.mp (by simpa using hm)) hx
    have hxa : x * a = a * x := mem_centralizer_singleton_iff.mp hxC.2
    rw [← hxa]
    group
  ·
    obtain ⟨r₀, hr₀⟩ := Subgroup.index_eq_two_iff.mp (show (C.subgroupOf R).index = 2 by
      simpa [Subgroup.relIndex] using hm)
    have hw : a * (r₀ : G)⁻¹ * a⁻¹ ∈ R :=
      (mem_normalizer_iff.mp ha _).mp (R.inv_mem r₀.2)
    have hβ : (r₀ : G) * (a * (r₀ : G)⁻¹ * a⁻¹) ∈ R := R.mul_mem r₀.2 hw
    refine ⟨(r₀ : G) * (a * (r₀ : G)⁻¹ * a⁻¹), hβ, fun x hx => ?_⟩
    rcases hr₀ ⟨x, hx⟩ with ⟨h1, -⟩ | ⟨h2, -⟩
    · right
      have h1' : x * (r₀ : G) ∈ C := by simpa [Subgroup.mem_subgroupOf] using h1
      have hxr : x * (r₀ : G) * a = a * (x * (r₀ : G)) :=
        mem_centralizer_singleton_iff.mp h1'.2
      calc a * x * a⁻¹ * x⁻¹
            = (a * (x * (r₀ : G))) * a⁻¹ * (a * (r₀ : G)⁻¹ * a⁻¹) * x⁻¹ := by group
        _ = (x * (r₀ : G) * a) * a⁻¹ * (a * (r₀ : G)⁻¹ * a⁻¹) * x⁻¹ := by rw [hxr]
        _ = x * ((r₀ : G) * (a * (r₀ : G)⁻¹ * a⁻¹)) * x⁻¹ := by group
        _ = ((r₀ : G) * (a * (r₀ : G)⁻¹ * a⁻¹)) * x * x⁻¹ := by rw [hcomm x hx _ hβ]
        _ = (r₀ : G) * (a * (r₀ : G)⁻¹ * a⁻¹) := by group
    · left
      have h2' : x ∈ C := by simpa [Subgroup.mem_subgroupOf] using h2
      have hxa : x * a = a * x := mem_centralizer_singleton_iff.mp h2'.2
      rw [← hxa]
      group

omit [Finite G] in
theorem a7r_conj_eq_self {R : Subgroup G} (hR : IsElemAbelian 2 R) {a β : G} (hβ : β ∈ R)
    (h : ∀ x ∈ R, a * x * a⁻¹ * x⁻¹ = 1 ∨ a * x * a⁻¹ * x⁻¹ = β) : a * β * a⁻¹ = β := by
  rcases h β hβ with h1 | h1
  · exact mul_inv_eq_one.mp h1
  · have h2 : a * β * a⁻¹ = β * β := mul_inv_eq_iff_eq_mul.mp h1
    have hββ : β * β = 1 := by rw [← pow_two]; exact hR.2 β hβ
    have hβ1 : β = 1 := by
      calc β = a⁻¹ * (a * β * a⁻¹) * a := by group
        _ = 1 := by rw [h2, hββ]; group
    rw [hβ1]
    group

omit [Finite G] in
theorem a7r_pow_twelve_of_comm_mem {R B : Subgroup G} (hR : IsElemAbelian 2 R) (hBR : B ≤ R)
    {g : G} (hg : ∀ x ∈ R, g * x * g⁻¹ * x⁻¹ ∈ B) (h6 : ∀ β ∈ B, g ^ 6 * β = β * g ^ 6) :
    g ^ 12 ∈ centralizer (R : Set G) := by
  have hpow : ∀ n : ℕ, ∀ x ∈ R, g ^ n * x * (g ^ n)⁻¹ * x⁻¹ ∈ B := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      have h1 := ih x hx
      have hy : g ^ n * x * (g ^ n)⁻¹ ∈ R := by
        have e : g ^ n * x * (g ^ n)⁻¹ = (g ^ n * x * (g ^ n)⁻¹ * x⁻¹) * x := by group
        rw [e]
        exact R.mul_mem (hBR h1) hx
      have h2 := hg _ hy
      have e : g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ * x⁻¹ =
          (g * (g ^ n * x * (g ^ n)⁻¹) * g⁻¹ * (g ^ n * x * (g ^ n)⁻¹)⁻¹) *
            (g ^ n * x * (g ^ n)⁻¹ * x⁻¹) := by
        rw [pow_succ']
        group
      rw [e]
      exact B.mul_mem h2 h1
  rw [mem_centralizer_iff]
  intro x hx
  have h1 := hpow 6 x hx
  have hββ : (g ^ 6 * x * (g ^ 6)⁻¹ * x⁻¹) * (g ^ 6 * x * (g ^ 6)⁻¹ * x⁻¹) = 1 := by
    rw [← pow_two]
    exact hR.2 _ (hBR h1)
  have hc := h6 _ h1
  have e : g ^ 12 * x * (g ^ 12)⁻¹ = x := by
    calc g ^ 12 * x * (g ^ 12)⁻¹
        = g ^ 6 * (g ^ 6 * x * (g ^ 6)⁻¹ * x⁻¹) * (g ^ 6)⁻¹ *
            ((g ^ 6 * x * (g ^ 6)⁻¹ * x⁻¹) * x) := by group
      _ = (g ^ 6 * x * (g ^ 6)⁻¹ * x⁻¹) * g ^ 6 * (g ^ 6)⁻¹ *
            ((g ^ 6 * x * (g ^ 6)⁻¹ * x⁻¹) * x) := by rw [hc]
      _ = ((g ^ 6 * x * (g ^ 6)⁻¹ * x⁻¹) * (g ^ 6 * x * (g ^ 6)⁻¹ * x⁻¹)) * x := by group
      _ = x := by rw [hββ, one_mul]
  exact (mul_inv_eq_iff_eq_mul.mp e).symm

omit [Finite G] in
theorem a7r_pow_six_commute {a b βa βb : G} (hc : βa * βb = βb * βa) (hsa : βa * βa = 1)
    (hsb : βb * βb = 1) (haa : a * βa * a⁻¹ = βa) (hbb : b * βb * b⁻¹ = βb)
    (hab : a * βb * a⁻¹ = βb ∨ a * βb * a⁻¹ = βa * βb)
    (hba : b * βa * b⁻¹ = βa ∨ b * βa * b⁻¹ = βb * βa) :
    Commute ((a * b) ^ 6) βa ∧ Commute ((a * b) ^ 6) βb := by
  have cm : ∀ x y z : G, x * (y * z) * x⁻¹ = (x * y * x⁻¹) * (x * z * x⁻¹) := fun x y z => by
    group
  have s2 : ∀ g y : G, g ^ 2 * y * (g ^ 2)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := fun g y => by
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
  have s3 : ∀ g y : G, g ^ 3 * y * (g ^ 3)⁻¹ = g * (g ^ 2 * y * (g ^ 2)⁻¹) * g⁻¹ :=
    fun g y => by simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
  have ga : (a * b) * βa * (a * b)⁻¹ = a * (b * βa * b⁻¹) * a⁻¹ := by group
  have gb : (a * b) * βb * (a * b)⁻¹ = a * βb * a⁻¹ := by
    rw [show (a * b) * βb * (a * b)⁻¹ = a * (b * βb * b⁻¹) * a⁻¹ by group, hbb]
  have up : ∀ k m : ℕ, k * m = 6 → ∀ y : G, (a * b) ^ k * y * ((a * b) ^ k)⁻¹ = y →
      Commute ((a * b) ^ 6) y := fun k m hkm y h => by
    have := Commute.pow_left (mul_inv_eq_iff_eq_mul.mp h) m
    rwa [← pow_mul, hkm] at this
  rcases hab with hab | hab <;> rcases hba with hba | hba
  ·
    have h1 : (a * b) * βa * (a * b)⁻¹ = βa := by rw [ga, hba, haa]
    have h2 : (a * b) * βb * (a * b)⁻¹ = βb := by rw [gb, hab]
    exact ⟨up 1 6 rfl _ (by rw [pow_one]; exact h1), up 1 6 rfl _ (by rw [pow_one]; exact h2)⟩
  ·
    have h1 : (a * b) * βa * (a * b)⁻¹ = βb * βa := by rw [ga, hba, cm, hab, haa]
    have h2 : (a * b) * βb * (a * b)⁻¹ = βb := by rw [gb, hab]
    have h3 : (a * b) ^ 2 * βa * ((a * b) ^ 2)⁻¹ = βa := by
      rw [s2, h1, cm, h2, h1, ← mul_assoc, hsb, one_mul]
    have h4 : (a * b) ^ 2 * βb * ((a * b) ^ 2)⁻¹ = βb := by rw [s2, h2, h2]
    exact ⟨up 2 3 rfl _ h3, up 2 3 rfl _ h4⟩
  ·
    have h1 : (a * b) * βa * (a * b)⁻¹ = βa := by rw [ga, hba, haa]
    have h2 : (a * b) * βb * (a * b)⁻¹ = βa * βb := by rw [gb, hab]
    have h3 : (a * b) ^ 2 * βa * ((a * b) ^ 2)⁻¹ = βa := by rw [s2, h1, h1]
    have h4 : (a * b) ^ 2 * βb * ((a * b) ^ 2)⁻¹ = βb := by
      rw [s2, h2, cm, h1, h2, ← mul_assoc, hsa, one_mul]
    exact ⟨up 2 3 rfl _ h3, up 2 3 rfl _ h4⟩
  ·
    have h1 : (a * b) * βa * (a * b)⁻¹ = βb := by
      rw [ga, hba, cm, hab, haa, hc, mul_assoc, hsa, mul_one]
    have h2 : (a * b) * βb * (a * b)⁻¹ = βa * βb := by rw [gb, hab]
    have h12 : (a * b) * (βa * βb) * (a * b)⁻¹ = βa := by
      rw [cm, h1, h2, ← mul_assoc, ← hc, mul_assoc, hsb, mul_one]
    have h3 : (a * b) ^ 3 * βa * ((a * b) ^ 3)⁻¹ = βa := by rw [s3, s2, h1, h2, h12]
    have h4 : (a * b) ^ 3 * βb * ((a * b) ^ 3)⁻¹ = βb := by rw [s3, s2, h2, h12, h1]
    exact ⟨up 3 2 rfl _ h3, up 3 2 rfl _ h4⟩

theorem a7r_pow_twelve_mem_centralizer {R : Subgroup G} (hR : IsElemAbelian 2 R) {a b : G}
    (ha : a ∈ normalizer (R : Set G)) (hb : b ∈ normalizer (R : Set G))
    (hca : Nat.card R < 4 * Nat.card (R ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hcb : Nat.card R < 4 * Nat.card (R ⊓ centralizer ({b} : Set G) : Subgroup G)) :
    (a * b) ^ 12 ∈ centralizer (R : Set G) := by
  obtain ⟨βa, hβa, hA⟩ := a7r_exists_transvection hR ha hca
  obtain ⟨βb, hβb, hB⟩ := a7r_exists_transvection hR hb hcb
  have hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hR.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ R, x * x = 1 := fun x hx => by rw [← pow_two]; exact hR.2 x hx
  set B : Subgroup G := closure {βa, βb}
  have hβaB : βa ∈ B := subset_closure (Set.mem_insert _ _)
  have hβbB : βb ∈ B := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hBR : B ≤ R :=
    (closure_le R).mpr (Set.insert_subset hβa (Set.singleton_subset_iff.mpr hβb))
  have haa := a7r_conj_eq_self hR hβa hA
  have hbb := a7r_conj_eq_self hR hβb hB
  have hab : a * βb * a⁻¹ = βb ∨ a * βb * a⁻¹ = βa * βb :=
    (hA βb hβb).imp mul_inv_eq_one.mp mul_inv_eq_iff_eq_mul.mp
  have hba : b * βa * b⁻¹ = βa ∨ b * βa * b⁻¹ = βb * βa :=
    (hB βa hβa).imp mul_inv_eq_one.mp mul_inv_eq_iff_eq_mul.mp
  have haB : ∀ β ∈ B, a * β * a⁻¹ ∈ B := by
    have hle : B ≤ B.comap (MulAut.conj a).toMonoidHom := by
      refine (closure_le _).mpr (Set.insert_subset ?_ (Set.singleton_subset_iff.mpr ?_))
      · show a * βa * a⁻¹ ∈ B
        rw [haa]
        exact hβaB
      · show a * βb * a⁻¹ ∈ B
        rcases hab with h | h <;> rw [h]
        · exact hβbB
        · exact B.mul_mem hβaB hβbB
    exact fun β hβ => hle hβ
  have hmem : ∀ x c β : G, (c * x * c⁻¹ * x⁻¹ = 1 ∨ c * x * c⁻¹ * x⁻¹ = β) → β ∈ B →
      c * x * c⁻¹ * x⁻¹ ∈ B := by
    rintro x c β (h | h) hβ <;> rw [h]
    · exact B.one_mem
    · exact hβ
  have hgB : ∀ x ∈ R, (a * b) * x * (a * b)⁻¹ * x⁻¹ ∈ B := by
    intro x hx
    have e : (a * b) * x * (a * b)⁻¹ * x⁻¹ =
        a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact B.mul_mem (haB _ (hmem x b βb (hB x hx) hβbB)) (hmem x a βa (hA x hx) hβaB)
  obtain ⟨h6a, h6b⟩ := a7r_pow_six_commute (hcomm βa hβa βb hβb) (hsq βa hβa) (hsq βb hβb)
    haa hbb hab hba
  have h6 : B ≤ centralizer ({(a * b) ^ 6} : Set G) :=
    (closure_le _).mpr (Set.insert_subset (mem_centralizer_singleton_iff.mpr h6a.eq.symm)
      (Set.singleton_subset_iff.mpr (mem_centralizer_singleton_iff.mpr h6b.eq.symm)))
  exact a7r_pow_twelve_of_comm_mem hR hBR hgB
    (fun β hβ => (mem_centralizer_singleton_iff.mp (h6 hβ)).symm)

omit [Finite G] in
theorem a7r_isElemAbelian_of_le {A B : Subgroup G} (hB : IsElemAbelian 2 B) (hAB : A ≤ B) :
    IsElemAbelian 2 A := CFSG.Open.IsElemAbelian.mono hB hAB

omit [Finite G] in
theorem a7r_a7W_le_centralizer (H : Subgroup G) :
    a7W H ≤ centralizer (pCoreOf 2 H : Set G) :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1.2

omit [Finite G] in
theorem a7r_mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

theorem a7r_card_centralizer_le {R : Subgroup G} {g : G} (hg : g ∈ normalizer (R : Set G))
    (a : G) : Nat.card (R ⊓ centralizer ({a} : Set G) : Subgroup G) ≤
      Nat.card (R ⊓ centralizer ({g * a * g⁻¹} : Set G) : Subgroup G) := by
  have hle : (R ⊓ centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom ≤
      R ⊓ centralizer ({g * a * g⁻¹} : Set G) := by
    rintro _ ⟨x, ⟨hxR, hxa⟩, rfl⟩
    have hxa' : x * a = a * x := mem_centralizer_singleton_iff.mp hxa
    refine ⟨(mem_normalizer_iff.mp hg x).mp hxR, mem_centralizer_singleton_iff.mpr ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
      _ = g * (a * x) * g⁻¹ := by rw [hxa']
      _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group
  calc Nat.card (R ⊓ centralizer ({a} : Set G) : Subgroup G)
      = Nat.card ((R ⊓ centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
    _ ≤ _ := Subgroup.card_le_of_le hle

omit [Finite G] in
theorem a7r_map_eq_one_iff {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) (h : ↥H) : ι h = 1 ↔ (h : G) ∈ a7K H := by
  rw [← MonoidHom.mem_ker, hF.ker_eq]
  exact (Subgroup.mem_map_iff_mem H.subtype_injective).symm

theorem a7r_isSolvable_a7K {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) : Group.IsSolvable (a7K H) := by
  have hSK : pCoreOf 2 H ≤ a7K H := hF.sylow.le
  set T : Subgroup (a7K H) := (pCoreOf 2 H).subgroupOf (a7K H)
  have hTn : T.Normal := (normal_subgroupOf_iff_le_normalizer hSK).mpr fun k hk => by
    rw [hF.H_norm]
    exact a7K_le H hk
  have hodd : Odd (Nat.card (a7K H ⧸ T)) := by
    rw [← Subgroup.index_eq_card]
    exact Nat.odd_iff.mpr
      (Nat.two_dvd_ne_zero.mp (CFSG.ABGLocalTools.isSylowOf_iff.mp hF.sylow).2.2)
  have hq : Group.IsSolvable (a7K H ⧸ T) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hTs : Group.IsSolvable T := by
    have h2 : IsPGroup 2 T := hF.sylow.isPGroup.comap_subtype
    have := h2.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range T.subtype (QuotientGroup.mk' T)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem a7r_isSimpleGroup_a7Five : IsSimpleGroup a7Five := by
  have he : a7Five =
      CFSG.RankThree.GroupTheory.alternatingOn ({0, 3, 4, 5, 6} : Finset (Fin 7)) := by
    ext σ
    rw [mem_a7Five_iff, CFSG.RankThree.GroupTheory.mem_alternatingOn_iff,
      Perm.mem_alternatingGroup]
    have hF : ∀ x : Fin 7, x ∉ ({0, 3, 4, 5, 6} : Finset (Fin 7)) → x = 1 ∨ x = 2 := by
      decide
    constructor
    · rintro ⟨hs, h1, h2⟩
      refine ⟨hs, fun x hx => ?_⟩
      rcases hF x hx with rfl | rfl
      · exact h1
      · exact h2
    · rintro ⟨hs, hfix⟩
      exact ⟨hs, hfix 1 (by decide), hfix 2 (by decide)⟩
  have := CFSG.RankThree.GroupTheory.alternatingOn_isSimpleGroup
    (F := ({0, 3, 4, 5, 6} : Finset (Fin 7))) (by decide)
  exact (MulEquiv.subgroupCongr he).isSimpleGroup

theorem a7r_eq_bot_or_eq_a7Five {M : Subgroup (Perm (Fin 7))} (hM : M ≤ a7Five)
    (hn : ∀ τ ∈ a7Five, ∀ m ∈ M, τ * m * τ⁻¹ ∈ M) : M = ⊥ ∨ M = a7Five := by
  have := a7r_isSimpleGroup_a7Five
  have hN : (M.subgroupOf a7Five).Normal :=
    (normal_subgroupOf_iff hM).mpr fun m τ hm hτ => hn τ hτ m hm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf a7Five) with h | h
  · left
    rw [subgroupOf_eq_bot] at h
    exact (Subgroup.eq_bot_iff_forall M).mpr fun m hm => Subgroup.disjoint_def.mp h hm (hM hm)
  · right
    exact le_antisymm hM (subgroupOf_eq_top.mp h)

theorem a7r_exists_conj : ∀ u ∈ vOne, u ≠ 1 → ∃ g ∈ a7Five, (u * (g * u * g⁻¹)) ^ 12 ≠ 1 := by
  have h1 : sw 0 3 * sw 4 5 ∈ a7Five := by
    rw [mem_a7Five_iff, Perm.mem_alternatingGroup]
    decide +kernel
  have h2 : sw 0 3 * sw 5 6 ∈ a7Five := by
    rw [mem_a7Five_iff, Perm.mem_alternatingGroup]
    decide +kernel
  rintro u ⟨i, rfl⟩ hu
  fin_cases i
  · exact absurd (by decide +kernel) hu
  · exact ⟨_, h1, by decide +kernel⟩
  · exact ⟨_, h2, by decide +kernel⟩
  · exact ⟨_, h2, by decide +kernel⟩

theorem a7r_map_eq_one_of_mem_centralizer {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) {Y₁ : Subgroup G} (hY₁I : Y₁ ≤ a7I H ι)
    (hY₁n : a7I H ι ≤ normalizer (Y₁ : Set G)) (hperf : Group.IsPerfect Y₁)
    (hι : (Y₁.subgroupOf H).map ι = a7Five) (hR0 : ⁅pCoreOf 2 H, Y₁⁆ ≠ ⊥)
    (hRY : ⁅(⁅pCoreOf 2 H, Y₁⁆ : Subgroup G), Y₁⁆ = ⁅pCoreOf 2 H, Y₁⁆) (y : ↥H)
    (hyY : (y : G) ∈ Y₁)
    (hyR : (y : G) ∈ centralizer ((⁅pCoreOf 2 H, Y₁⁆ : Subgroup G) : Set G)) :
    ι y = 1 := by
  set R : Subgroup G := ⁅pCoreOf 2 H, Y₁⁆
  have hY₁H : Y₁ ≤ H := hY₁I.trans (a7I_le H ι)
  have hYR : ∀ z ∈ Y₁, z ∈ normalizer (R : Set G) := fun z hz =>
    a7r_mem_normalizer_commutator (by rw [hF.H_norm]; exact hY₁H hz) (hY₁n (hY₁I hz))
  set C : Subgroup G := centralizer (R : Set G) ⊓ Y₁
  have hCn : ∀ z ∈ Y₁, ∀ c ∈ C, z * c * z⁻¹ ∈ C := by
    intro z hz c hc
    refine ⟨mem_centralizer_iff.mpr ?_, Y₁.mul_mem (Y₁.mul_mem hz hc.2) (Y₁.inv_mem hz)⟩
    intro r hr
    have hr' : z⁻¹ * r * z ∈ R := by
      rw [mem_normalizer_iff.mp (hYR z hz) (z⁻¹ * r * z)]
      simpa [mul_assoc] using hr
    have hcr := mem_centralizer_iff.mp hc.1 _ hr'
    calc r * (z * c * z⁻¹) = z * ((z⁻¹ * r * z) * c) * z⁻¹ := by group
      _ = z * (c * (z⁻¹ * r * z)) * z⁻¹ := by rw [hcr]
      _ = z * c * z⁻¹ * r := by group
  set M : Subgroup (Perm (Fin 7)) := (C.subgroupOf H).map ι
  have hMle : M ≤ a7Five := by
    rw [← hι]
    exact map_mono (subgroupOf_mono H inf_le_right)
  have hMn : ∀ τ ∈ a7Five, ∀ m ∈ M, τ * m * τ⁻¹ ∈ M := by
    intro τ hτ m hm
    rw [← hι] at hτ
    obtain ⟨z, hz, rfl⟩ := hτ
    obtain ⟨c, hc, rfl⟩ := hm
    exact ⟨z * c * z⁻¹, hCn z hz c hc, by simp only [map_mul, map_inv]⟩
  have hyM : ι y ∈ M := ⟨y, ⟨hyR, hyY⟩, rfl⟩
  rcases a7r_eq_bot_or_eq_a7Five hMle hMn with hM0 | hMA
  · rw [hM0] at hyM
    exact Subgroup.mem_bot.mp hyM
  exfalso
  apply hR0
  suffices hY : Y₁ ≤ centralizer (R : Set G) by
    rw [← hRY]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hY)
  have hK := a7r_isSolvable_a7K hF
  set N : Subgroup Y₁ := C.subgroupOf Y₁
  have hNn : N.Normal := (normal_subgroupOf_iff inf_le_right).mpr fun c z hc hz => hCn z hz c hc
  set L : Subgroup Y₁ := (a7K H).subgroupOf Y₁
  have hLs : Group.IsSolvable L := by
    let f : L →* a7K H :=
      { toFun := fun z => ⟨((z : Y₁) : G), z.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun z w hzw => ?_
    have := congrArg Subtype.val hzw
    exact Subtype.ext (Subtype.ext this)
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp L.subtype) := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    have hzM : ι ⟨z, hY₁H z.2⟩ ∈ M := by
      rw [hMA, ← hι]
      exact ⟨⟨z, hY₁H z.2⟩, z.2, rfl⟩
    obtain ⟨c, hc, hcz⟩ := hzM
    have hcY : (c : G) ∈ Y₁ := hc.2
    refine ⟨⟨z * ⟨c, hcY⟩⁻¹, ?_⟩, ?_⟩
    · show (z : G) * (c : G)⁻¹ ∈ a7K H
      have h1 : ι (⟨z, hY₁H z.2⟩ * c⁻¹) = 1 := by rw [map_mul, map_inv, ← hcz, mul_inv_cancel]
      exact (a7r_map_eq_one_iff hF _).mp h1
    · simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, Subgroup.coe_subtype]
      rw [QuotientGroup.eq]
      have e : (z * ⟨c, hcY⟩⁻¹)⁻¹ * z = ⟨c, hcY⟩ := by group
      rw [e]
      exact hc
  have hQs : Group.IsSolvable (Y₁ ⧸ N) := Group.isSolvable_of_surjective hsurj
  have hQsub : Subsingleton (Y₁ ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable (Y₁ ⧸ N) hQs
  intro z hz
  have h1 : (QuotientGroup.mk (⟨z, hz⟩ : Y₁) : Y₁ ⧸ N) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff] at h1
  exact h1.1

theorem A7Frame.rank_ge_four {D H V : Subgroup G} {ι : ↥H →* Perm (Fin 7)}
    (hF : A7Frame D H V ι) {Y₁ : Subgroup G} (hY₁I : Y₁ ≤ a7I H ι)
    (hY₁n : a7I H ι ≤ normalizer (Y₁ : Set G)) (hperf : Group.IsPerfect Y₁)
    (hι : (Y₁.subgroupOf H).map ι = a7Five) (hVY : V ≤ Y₁ ⊔ pCoreOf 2 H)
    (hRW : ⁅pCoreOf 2 H, Y₁⁆ ≤ a7W H) (hR0 : ⁅pCoreOf 2 H, Y₁⁆ ≠ ⊥)
    (hRY : ⁅(⁅pCoreOf 2 H, Y₁⁆ : Subgroup G), Y₁⁆ = ⁅pCoreOf 2 H, Y₁⁆)
    {a : G} (haV : a ∈ V) (ha2 : a ^ 2 = 1) (haS : a ∉ pCoreOf 2 H) :
    4 * Nat.card (⁅pCoreOf 2 H, Y₁⁆ ⊓ centralizer ({a} : Set G) : Subgroup G) ≤
      Nat.card (⁅pCoreOf 2 H, Y₁⁆ : Subgroup G) := by
  by_contra hlt
  rw [not_le] at hlt
  have hY₁H : Y₁ ≤ H := hY₁I.trans (a7I_le H ι)
  have hHS : ∀ g ∈ H, g ∈ normalizer (pCoreOf 2 H : Set G) := fun g hg => by
    rw [hF.H_norm]
    exact hg
  have hKI : a7K H ≤ a7I H ι := fun k hk => mem_a7I_iff.mpr
    ⟨⟨k, a7K_le H hk⟩, by rw [(a7r_map_eq_one_iff hF ⟨k, a7K_le H hk⟩).mpr hk]; exact one_mem _,
      rfl⟩
  have hNI : Y₁ ⊔ pCoreOf 2 H ≤ a7I H ι := sup_le hY₁I (hF.sylow.le.trans hKI)
  have hIR : ∀ g ∈ a7I H ι, g ∈ normalizer ((⁅pCoreOf 2 H, Y₁⁆ : Subgroup G) : Set G) :=
    fun g hg => a7r_mem_normalizer_commutator (hHS g (a7I_le H ι hg)) (hY₁n hg)
  have hRe : IsElemAbelian 2 ⁅pCoreOf 2 H, Y₁⁆ :=
    a7r_isElemAbelian_of_le (CFSG.Quasithin.B2F.isElemAbelian_omegaOneCenterOf _) hRW
  have hSR : ∀ s ∈ pCoreOf 2 H, s ∈ centralizer ((⁅pCoreOf 2 H, Y₁⁆ : Subgroup G) : Set G) :=
    fun s hs => mem_centralizer_iff.mpr fun r hr =>
      (mem_centralizer_iff.mp (a7r_a7W_le_centralizer H (hRW hr)) s hs).symm
  have haH : a ∈ H := hF.V_le haV
  have haI : a ∈ a7I H ι := hNI (hVY haV)
  have huV : ι ⟨a, haH⟩ ∈ vOne := by
    rw [← hF.V_img]
    exact ⟨⟨a, haH⟩, haV, rfl⟩
  have hu1 : ι ⟨a, haH⟩ ≠ 1 := by
    intro h1
    have haK : a ∈ a7K H := (a7r_map_eq_one_iff hF ⟨a, haH⟩).mp h1
    have hTa : IsPGroup 2 (zpowers a) := fun x => ⟨1, Subtype.ext (by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp x.2
      rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, ha2, one_zpow, Subgroup.coe_one])⟩
    exact haS (le_of_isSylowOf_of_normalizer hF.sylow (fun k hk => hHS k (a7K_le H hk))
      (zpowers_le.mpr haK) hTa (mem_zpowers a))
  obtain ⟨g, hgA, hg12⟩ := a7r_exists_conj _ huV hu1
  rw [← hι] at hgA
  obtain ⟨h, hhY, rfl⟩ := hgA
  have hhY' : (h : G) ∈ Y₁ := hhY
  have ha₂I : (h : G) * a * (h : G)⁻¹ ∈ a7I H ι :=
    (a7I H ι).mul_mem ((a7I H ι).mul_mem (hY₁I hhY') haI) ((a7I H ι).inv_mem (hY₁I hhY'))
  have hca₂ : Nat.card (⁅pCoreOf 2 H, Y₁⁆ : Subgroup G) < 4 * Nat.card
      (⁅pCoreOf 2 H, Y₁⁆ ⊓ centralizer ({(h : G) * a * (h : G)⁻¹} : Set G) : Subgroup G) :=
    lt_of_lt_of_le hlt (Nat.mul_le_mul_left 4 (a7r_card_centralizer_le (hIR _ (hY₁I hhY')) a))
  have hx := a7r_pow_twelve_mem_centralizer hRe (hIR a haI) (hIR _ ha₂I) hlt hca₂
  have hxN : (a * ((h : G) * a * (h : G)⁻¹)) ^ 12 ∈ Y₁ ⊔ pCoreOf 2 H := by
    have hhN : (h : G) ∈ Y₁ ⊔ pCoreOf 2 H := mem_sup_left hhY'
    have haN := hVY haV
    exact pow_mem (mul_mem haN (mul_mem (mul_mem hhN haN) (inv_mem hhN))) 12
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right Y₁ (pCoreOf 2 H)
    (fun y hy => hHS y (hY₁H hy))] at hxN
  obtain ⟨y, hyY, s, hsS, hys⟩ := Set.mem_mul.mp hxN
  have hyR : y ∈ centralizer ((⁅pCoreOf 2 H, Y₁⁆ : Subgroup G) : Set G) := by
    have e : y = (a * ((h : G) * a * (h : G)⁻¹)) ^ 12 * s⁻¹ := by
      rw [← hys]
      group
    rw [e]
    exact mul_mem hx (inv_mem (hSR s hsS))
  have hy1 := a7r_map_eq_one_of_mem_centralizer hF hY₁I hY₁n hperf hι hR0 hRY ⟨y, hY₁H hyY⟩
    hyY hyR
  have hsH : s ∈ H := a7K_le H (hF.sylow.le hsS)
  have hs1 : ι ⟨s, hsH⟩ = 1 := (a7r_map_eq_one_iff hF ⟨s, hsH⟩).mpr (hF.sylow.le hsS)
  apply hg12
  have e : (⟨a, haH⟩ * (h * ⟨a, haH⟩ * h⁻¹)) ^ 12 = (⟨y, hY₁H hyY⟩ * ⟨s, hsH⟩ : ↥H) := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hys.symm
  calc (ι ⟨a, haH⟩ * (ι h * ι ⟨a, haH⟩ * (ι h)⁻¹)) ^ 12
      = ι ((⟨a, haH⟩ * (h * ⟨a, haH⟩ * h⁻¹)) ^ 12) := by simp only [map_pow, map_mul, map_inv]
    _ = 1 := by rw [e, map_mul, hy1, hs1, mul_one]

end CFSG.LocalAnalysis.RankThreeTheoremC
