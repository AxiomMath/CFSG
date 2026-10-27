module

public import CFSG.Goldschmidt.StatementsG4
import CFSG.Goldschmidt.Steps.G75Basic
import CFSG.Goldschmidt.Steps.G3aBorel
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.Walter.Bender1970.S2.PGroup
public import CFSG.Goldschmidt.StatementsG

public section

namespace CFSG.Goldschmidt.G75

open CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Bezout

omit [Finite G] in
theorem mem_of_pow_mem_of_pow_seven_mem {M : Subgroup G} {y : G} {m : ℕ} (hm : y ^ m ∈ M)
    (h7 : y ^ 7 ∈ M) (hm7 : ¬ 7 ∣ m) : y ∈ M := by
  have hcop : Nat.Coprime m 7 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]
    exact hm7
  have hg := Nat.gcd_eq_gcd_ab m 7
  rw [hcop, Nat.cast_one] at hg
  have : y = (y ^ m) ^ (Nat.gcdA m 7) * (y ^ 7) ^ (Nat.gcdB m 7) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg, zpow_one]
  rw [this]
  exact M.mul_mem (M.zpow_mem hm _) (M.zpow_mem h7 _)

end Bezout

section Card

variable {A : Subgroup G}

omit [Finite G] in
theorem conjSub_commutator_eq {y : G} (hy : y ∈ Subgroup.normalizer (A : Set G)) :
    conjSub y ⁅A, Subgroup.zpowers y⁆ = ⁅A, Subgroup.zpowers y⁆ := by
  unfold conjSub
  rw [Subgroup.map_commutator]
  have h1 : A.map (MulAut.conj y⁻¹).toMonoidHom = A := by
    have := conjSub_eq_of_mem_normalizer hy
    unfold conjSub at this
    exact this
  have h2 : (Subgroup.zpowers y).map (MulAut.conj y⁻¹).toMonoidHom = Subgroup.zpowers y := by
    rw [MonoidHom.map_zpowers]
    simp
  rw [h1, h2]

omit [Finite G] in
theorem mem_normalizer_commutator {y : G} (hy : y ∈ Subgroup.normalizer (A : Set G)) :
    y ∈ Subgroup.normalizer ((⁅A, Subgroup.zpowers y⁆ : Subgroup G) : Set G) := by
  have h := conjSub_commutator_eq hy
  have h' : y⁻¹ ∈ Subgroup.normalizer ((⁅A, Subgroup.zpowers y⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have : y⁻¹ * z * y⁻¹⁻¹ ∈ conjSub y ⁅A, Subgroup.zpowers y⁆ := by
        rw [mem_conjSub]; simpa [mul_assoc] using hz
      rwa [h] at this
    · intro hz
      rw [← h] at hz
      simpa [mul_assoc] using mem_conjSub.1 hz
  simpa using (Subgroup.normalizer _).inv_mem h'

omit [Finite G] in
theorem pow_conj_mem {B : Subgroup G} {y : G} (hy : y ∈ Subgroup.normalizer (B : Set G))
    (k : ℕ) {b : G} (hb : b ∈ B) : (y ^ k)⁻¹ * b * y ^ k ∈ B := by
  have hk : (y ^ k)⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normalizer _).inv_mem ((Subgroup.normalizer _).pow_mem hy k)
  simpa using (Subgroup.mem_normalizer_iff.1 hk b).1 hb

omit [Finite G] in
theorem pow_conj_mod_seven {y b : G} (h7 : y ^ 7 * b = b * y ^ 7) (k : ℕ) :
    (y ^ k)⁻¹ * b * y ^ k = (y ^ (k % 7))⁻¹ * b * y ^ (k % 7) := by
  conv_lhs => rw [← Nat.mod_add_div k 7, pow_add, pow_mul]
  have hc : (y ^ 7) ^ (k / 7) * b = b * (y ^ 7) ^ (k / 7) :=
    ((Commute.pow_left (h7 : Commute (y ^ 7) b) (k / 7)))
  rw [mul_inv_rev]
  calc ((y ^ 7) ^ (k / 7))⁻¹ * (y ^ (k % 7))⁻¹ * b * (y ^ (k % 7) * (y ^ 7) ^ (k / 7))
      = ((y ^ 7) ^ (k / 7))⁻¹ * ((y ^ (k % 7))⁻¹ * b * y ^ (k % 7)) * (y ^ 7) ^ (k / 7) := by
        group
    _ = (y ^ (k % 7))⁻¹ * b * y ^ (k % 7) := by
        have hcy : Commute ((y ^ 7) ^ (k / 7)) (y ^ (k % 7)) :=
          (((Commute.refl y).pow_left 7).pow_left (k / 7)).pow_right (k % 7)
        have hc' : Commute ((y ^ 7) ^ (k / 7)) ((y ^ (k % 7))⁻¹ * b * y ^ (k % 7)) :=
          Commute.mul_right (Commute.mul_right hcy.inv_right hc) hcy
        rw [hc'.inv_left.eq]
        group

theorem card_commutator_eq_eight (hA : IsElemAbelian 2 A) {y : G}
    (hyN : y ∈ Subgroup.normalizer (A : Set G)) (hodd : Odd (orderOf y))
    (hy1 : y ∉ Subgroup.centralizer (A : Set G)) (hy7 : y ^ 7 ∈ Subgroup.centralizer (A : Set G))
    (htrans : ∀ b ∈ ⁅A, Subgroup.zpowers y⁆, ∀ c ∈ ⁅A, Subgroup.zpowers y⁆, b ≠ 1 → c ≠ 1 →
      ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c) :
    Nat.card (⁅A, Subgroup.zpowers y⁆ : Subgroup G) = 8 := by
  set B₀ := ⁅A, Subgroup.zpowers y⁆ with hB₀
  have hB₀A : B₀ ≤ A := commutator_zpowers_le_self hyN
  have hdisj := commutator_inf_centralizer_eq_bot hA hyN hodd
  have hne : B₀ ≠ ⊥ := by
    intro h
    apply hy1
    have h1 := (coprime_decomp hA hyN hodd).1
    rw [← hB₀, h, sup_bot_eq] at h1
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← h1] at hb
    exact Subgroup.mem_centralizer_singleton_iff.1 hb.2
  obtain ⟨⟨b, hbB⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hyB := mem_normalizer_commutator hyN
  have h7b : ∀ c ∈ A, y ^ 7 * c = c * y ^ 7 := fun c hc =>
    (Subgroup.mem_centralizer_iff.1 hy7 c hc).symm
  let f : Option (Fin 7) → B₀ := fun o => match o with
    | none => 1
    | some k => ⟨(y ^ (k : ℕ))⁻¹ * b * y ^ (k : ℕ), pow_conj_mem hyB k hbB⟩
  have hf1 : ∀ k : Fin 7, (y ^ (k : ℕ))⁻¹ * b * y ^ (k : ℕ) ≠ 1 := by
    intro k h
    apply hb1'
    have : b = y ^ (k : ℕ) * ((y ^ (k : ℕ))⁻¹ * b * y ^ (k : ℕ)) * (y ^ (k : ℕ))⁻¹ := by group
    rw [this, h]; group
  have hinj : ∀ i j : Fin 7, (y ^ (i : ℕ))⁻¹ * b * y ^ (i : ℕ) =
      (y ^ (j : ℕ))⁻¹ * b * y ^ (j : ℕ) → i = j := by
    have key : ∀ i j : Fin 7, (i : ℕ) < j → (y ^ (i : ℕ))⁻¹ * b * y ^ (i : ℕ) =
        (y ^ (j : ℕ))⁻¹ * b * y ^ (j : ℕ) → False := by
      intro i j hij h
      have hm : y ^ ((j : ℕ) - i) ∈ Subgroup.centralizer ({b} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hj : (j : ℕ) = i + ((j : ℕ) - i) := by omega
        rw [hj, pow_add] at h
        have : b = (y ^ ((j : ℕ) - i))⁻¹ * b * y ^ ((j : ℕ) - i) := by
          have h' := congrArg (fun z => y ^ (i : ℕ) * z * (y ^ (i : ℕ))⁻¹) h
          simp only [mul_inv_rev] at h'
          calc b = y ^ (i : ℕ) * ((y ^ (i : ℕ))⁻¹ * b * y ^ (i : ℕ)) * (y ^ (i : ℕ))⁻¹ := by
                group
            _ = _ := h'
            _ = (y ^ ((j : ℕ) - i))⁻¹ * b * y ^ ((j : ℕ) - i) := by group
        calc y ^ ((j : ℕ) - i) * b
            = y ^ ((j : ℕ) - i) * ((y ^ ((j : ℕ) - i))⁻¹ * b * y ^ ((j : ℕ) - i)) := by
              rw [← this]
          _ = b * y ^ ((j : ℕ) - i) := by group
      have h7' : y ^ 7 ∈ Subgroup.centralizer ({b} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact h7b b (hB₀A hbB)
      have hnd : ¬ 7 ∣ ((j : ℕ) - i) := by
        intro hd
        have h1 : 0 < (j : ℕ) - i := by omega
        have h2 : (j : ℕ) - i < 7 := by omega
        exact absurd (Nat.le_of_dvd h1 hd) (by omega)
      have hyb := mem_of_pow_mem_of_pow_seven_mem hm h7' hnd
      have hbC : b ∈ Subgroup.centralizer ({y} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 hyb).symm
      have : b ∈ B₀ ⊓ Subgroup.centralizer ({y} : Set G) := ⟨hbB, hbC⟩
      rw [hdisj] at this
      exact hb1' this
    intro i j h
    rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
    · exact (key i j hij h).elim
    · exact Fin.ext hij
    · exact (key j i hij h.symm).elim
  have hbij : Function.Bijective f := by
    constructor
    · rintro (_ | i) (_ | j) h
      · rfl
      · exact absurd (congrArg Subtype.val h).symm (hf1 j)
      · exact absurd (congrArg Subtype.val h) (hf1 i)
      · exact congrArg some (hinj i j (congrArg Subtype.val h))
    · rintro ⟨c, hc⟩
      by_cases hc1 : c = 1
      · exact ⟨none, Subtype.ext hc1.symm⟩
      · obtain ⟨k, hk⟩ := htrans b hbB c hc hb1' hc1
        refine ⟨some ⟨k % 7, Nat.mod_lt _ (by norm_num)⟩, Subtype.ext ?_⟩
        show (y ^ (k % 7))⁻¹ * b * y ^ (k % 7) = c
        rw [← pow_conj_mod_seven (h7b b (hB₀A hbB)) k, hk]
  rw [← Nat.card_eq_of_bijective f hbij]
  simp

end Card


section Sz8

theorem commutator_mem_centralizer_of_sz8
    {K : Subgroup G}
    (hq : GorensteinWalter.IsQuasisimple K) (hcov : Nonempty (K ⧸ Subgroup.center K ≃* Sz 1))
    {T : Subgroup G} (hTK : T ≤ K) (hT2 : IsPGroup 2 T) {b : G} (hbT : b ∈ T) (hb2 : b ^ 2 = 1)
    {t : G} (ht : t ∈ T) : t⁻¹ * b * t * b⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2.2
  have : Group.IsPerfect K := ⟨hq.2.1⟩
  set L := K ⧸ Subgroup.center K
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  have hcenter : Subgroup.center L = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot K
  have hI : IsGoldTypeI L := Or.inr (Or.inl ⟨1, le_rfl,
    ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientBot.trans hcov.some)⟩⟩)
  have hT' : IsPGroup 2 (T.subgroupOf K) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  obtain ⟨S', hS'⟩ := hT'.exists_le_sylow
  set S'' := S'.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center K)) with hS''
  obtain ⟨-, -, -, -, -, -, -, -, hΩ, -⟩ := G32 L hI S''
  have hb : (⟨b, hTK hbT⟩ : K) ∈ (S' : Subgroup K) := hS' (by simpa [Subgroup.mem_subgroupOf])
  have ht' : (⟨t, hTK ht⟩ : K) ∈ (S' : Subgroup K) := hS' (by simpa [Subgroup.mem_subgroupOf])
  have hbS : π ⟨b, hTK hbT⟩ ∈ (S'' : Subgroup L) := by
    rw [hS'', Sylow.coe_mapSurjective]; exact ⟨_, hb, rfl⟩
  have htS : π ⟨t, hTK ht⟩ ∈ (S'' : Subgroup L) := by
    rw [hS'', Sylow.coe_mapSurjective]; exact ⟨_, ht', rfl⟩
  have hbΩ : π ⟨b, hTK hbT⟩ ∈ Omega1 (S'' : Subgroup L) := by
    refine Subgroup.subset_closure ⟨hbS, ?_⟩
    rw [← map_pow]
    have : (⟨b, hTK hbT⟩ : K) ^ 2 = 1 := Subtype.ext (by simpa using hb2)
    rw [this, map_one]
  rw [hΩ] at hbΩ
  have hcomm : π ⟨t, hTK ht⟩ * π ⟨b, hTK hbT⟩ = π ⟨b, hTK hbT⟩ * π ⟨t, hTK ht⟩ :=
    (Subgroup.mem_centralizer_iff.1 hbΩ.2 _ htS)
  have hz : (⟨t, hTK ht⟩ : K)⁻¹ * ⟨b, hTK hbT⟩ * ⟨t, hTK ht⟩ * (⟨b, hTK hbT⟩ : K)⁻¹ ∈
      Subgroup.center K := by
    rw [← QuotientGroup.eq_one_iff]
    change π _ = 1
    simp only [map_mul, map_inv]
    calc (π ⟨t, hTK ht⟩)⁻¹ * π ⟨b, hTK hbT⟩ * π ⟨t, hTK ht⟩ * (π ⟨b, hTK hbT⟩)⁻¹
        = (π ⟨t, hTK ht⟩)⁻¹ * (π ⟨b, hTK hbT⟩ * π ⟨t, hTK ht⟩) * (π ⟨b, hTK hbT⟩)⁻¹ := by
          group
      _ = (π ⟨t, hTK ht⟩)⁻¹ * (π ⟨t, hTK ht⟩ * π ⟨b, hTK hbT⟩) * (π ⟨b, hTK hbT⟩)⁻¹ := by
          rw [hcomm]
      _ = 1 := by group
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have := Subgroup.mem_center_iff.1 hz ⟨k, hk⟩
  simpa using congrArg Subtype.val this

end Sz8


section Transvection

variable {V : Type} [Group V] [Finite V]

omit [Finite V] in
theorem fix_of_pow_fix {s : MulAut V} (hs7 : s ^ 7 = 1) {b : V} {m : ℕ} (hm : (s ^ m) b = b)
    (hm7 : ¬ 7 ∣ m) : s b = b := by
  let M : Subgroup (MulAut V) := MulAction.stabilizer (MulAut V) b
  have h1 : s ^ m ∈ M := hm
  have h2 : s ^ 7 ∈ M := by rw [hs7]; exact M.one_mem
  exact mem_of_pow_mem_of_pow_seven_mem h1 h2 hm7

omit [Finite V] in
theorem seven_dvd_of_pow_apply_eq {s : MulAut V} (hs7 : s ^ 7 = 1) {b : V} (hsb : s b ≠ b)
    {i j : ℕ} (hij : j ≤ i) (h : (s ^ i) b = (s ^ j) b) : 7 ∣ i - j := by
  by_contra hd
  apply hsb
  refine fix_of_pow_fix hs7 (m := i - j) ?_ hd
  have : s ^ i = s ^ j * s ^ (i - j) := by rw [← pow_add]; congr 1; omega
  rw [this, MulAut.mul_apply] at h
  exact (s ^ j).injective h

theorem false_of_transvection (hcomm : ∀ u w : V, u * w = w * u) (hsq : ∀ u : V, u * u = 1)
    {a₀ : V} {B₀ : Subgroup V} (ha₀B : a₀ ∉ B₀)
    (hdec : ∀ u : V, u ∈ B₀ ∨ a₀ * u ∈ B₀) (hB8 : Nat.card B₀ = 8)
    {s : MulAut V} (hsB : ∀ b ∈ B₀, s b ∈ B₀) (hs7 : s ^ 7 = 1)
    (hstrans : ∀ b ∈ B₀, ∀ c ∈ B₀, b ≠ 1 → c ≠ 1 → ∃ k : ℕ, (s ^ k) b = c)
    (hsfix : ∀ b ∈ B₀, b ≠ 1 → s b ≠ b)
    {Y : Subgroup (MulAut V)} (hY : Nat.card Y = 56) (hsY : s ∈ Y)
    {Q : Subgroup (MulAut V)} (hQY : Q ≤ Y) (hQ : 8 ≤ Nat.card Q)
    (hQa : ∀ σ ∈ Q, ∀ u, σ u * u⁻¹ = 1 ∨ σ u * u⁻¹ = a₀) (hYa : ∀ σ ∈ Y, σ a₀ = a₀)
    {τ : MulAut V} (hτ1 : τ ≠ 1) (hτa : τ a₀ = a₀) {v : V} (hvB : v ∈ B₀) (hv1 : v ≠ 1)
    (hτv : ∀ u, τ u * u⁻¹ = 1 ∨ τ u * u⁻¹ = v) (hτY : ∀ σ ∈ Y, τ * σ * τ⁻¹ ∈ Y) : False := by
  classical
  have := Fintype.ofFinite V
  have hinvV : ∀ u : V, u⁻¹ = u := fun u => inv_eq_of_mul_eq_one_right (hsq u)
  obtain ⟨b₀, hb₀B, hb₀1⟩ : ∃ b ∈ B₀, b ≠ 1 := by
    by_contra h
    push Not at h
    have : B₀ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    rw [this, Subgroup.card_bot] at hB8
    omega
  have hid : ∀ σ : MulAut V, σ a₀ = a₀ → (∀ b ∈ B₀, σ b = b) → σ = 1 := by
    intro σ hσa hσB
    ext u
    rcases hdec u with hu | hu
    · exact hσB u hu
    · have h := hσB _ hu
      rw [map_mul, hσa] at h
      simpa using mul_left_cancel h
  have hspow : ∀ i j : ℕ, i < 7 → j < 7 → s ^ i = s ^ j → i = j := by
    intro i j hi hj h
    have hsb := hsfix b₀ hb₀B hb₀1
    have key : ∀ i j : ℕ, j ≤ i → i < 7 → s ^ i = s ^ j → i = j := by
      intro i j hji hi h
      have h7 := seven_dvd_of_pow_apply_eq hs7 hsb hji (by rw [h])
      have : i - j < 7 := by omega
      omega
    rcases le_total j i with hji | hij
    · exact key i j hji hi h
    · exact (key j i hij hj h.symm).symm
  have hQB : ∀ σ ∈ Q, (∀ b ∈ B₀, σ b ∈ B₀) → σ = 1 := by
    intro σ hσ hσB
    refine hid σ (hYa σ (hQY hσ)) fun b hb => ?_
    rcases hQa σ hσ b with h | h
    · exact mul_inv_eq_one.1 h
    · exfalso
      apply ha₀B
      rw [← h]
      exact B₀.mul_mem (hσB b hb) (B₀.inv_mem hb)
  have hpowB : ∀ k : ℕ, ∀ b ∈ B₀, (s ^ k) b ∈ B₀ := by
    intro k
    induction k with
    | zero => intro b hb; simpa using hb
    | succ k ih => intro b hb; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hsB b hb)
  let F : Fin 7 × Q → Y := fun p => ⟨s ^ (p.1 : ℕ) * p.2, Y.mul_mem (Y.pow_mem hsY _)
    (hQY p.2.2)⟩
  have hFinj : Function.Injective F := by
    rintro ⟨i, q⟩ ⟨j, q'⟩ h
    have h' : s ^ (i : ℕ) * (q : MulAut V) = s ^ (j : ℕ) * q' := congrArg Subtype.val h
    have hq : (q' : MulAut V) * (q : MulAut V)⁻¹ = (s ^ (j : ℕ))⁻¹ * s ^ (i : ℕ) := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h', mul_inv_cancel_right]
    have hpres : ∀ b ∈ B₀, ((q' : MulAut V) * (q : MulAut V)⁻¹) b ∈ B₀ := by
      intro b hb
      rw [hq]
      have hsj : ((s ^ (j : ℕ))⁻¹) ((s ^ (i : ℕ)) b) =
          (s ^ (7 - (j : ℕ))) ((s ^ (i : ℕ)) b) := by
        congr 1
        rw [inv_eq_iff_mul_eq_one, ← pow_add]
        have : (j : ℕ) + (7 - (j : ℕ)) = 7 := by omega
        rw [this, hs7]
      rw [MulAut.mul_apply, hsj]
      exact hpowB _ _ (hpowB _ _ hb)
    have h1 := hQB _ (Q.mul_mem q'.2 (Q.inv_mem q.2)) hpres
    have hqq : (q' : MulAut V) = q := by rw [mul_inv_eq_one] at h1; exact h1
    have hij : (i : ℕ) = j := by
      apply hspow _ _ i.2 j.2
      rw [hqq] at h'
      exact mul_right_cancel h'
    exact Prod.ext (Fin.ext hij) (Subtype.ext hqq.symm)
  have hcardFY : Nat.card (Fin 7 × Q) = Nat.card Y := by
    have hle := Nat.card_le_card_of_injective F hFinj
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 7), Fintype.card_fin, hY] at hle ⊢
    omega
  have hFsurj : Function.Surjective F := by
    have := (Function.Injective.bijective_of_nat_card_le hFinj hcardFY.ge)
    exact this.2
  have hYB : ∀ σ ∈ Y, (∀ b ∈ B₀, σ b ∈ B₀) → ∃ k : ℕ, k < 7 ∧ σ = s ^ k := by
    intro σ hσ hσB
    obtain ⟨⟨k, q⟩, hkq⟩ := hFsurj ⟨σ, hσ⟩
    have hkq' : s ^ (k : ℕ) * (q : MulAut V) = σ := congrArg Subtype.val hkq
    have hq1 : (q : MulAut V) = 1 := by
      refine hQB q q.2 fun b hb => ?_
      have hqb : (q : MulAut V) = (s ^ (k : ℕ))⁻¹ * σ := by rw [← hkq', inv_mul_cancel_left]
      have hsk : ((s ^ (k : ℕ))⁻¹) (σ b) = (s ^ (7 - (k : ℕ))) (σ b) := by
        congr 1
        rw [inv_eq_iff_mul_eq_one, ← pow_add]
        have : (k : ℕ) + (7 - (k : ℕ)) = 7 := by omega
        rw [this, hs7]
      rw [hqb, MulAut.mul_apply, hsk]
      exact hpowB _ _ (hσB b hb)
    exact ⟨k, k.2, by rw [← hkq', hq1, mul_one]⟩
  have hτv' : τ v = v := by
    rcases hτv v with h | h
    · exact mul_inv_eq_one.1 h
    · exfalso
      have : τ v = v * v := mul_inv_eq_iff_eq_mul.1 h
      rw [hsq v] at this
      exact hv1 (τ.injective (by rw [this, map_one]))
  have hτB : ∀ b ∈ B₀, τ b ∈ B₀ := by
    intro b hb
    rcases hτv b with h | h
    · rw [mul_inv_eq_one.1 h]; exact hb
    · have : τ b = v * b := mul_inv_eq_iff_eq_mul.1 h
      rw [this]; exact B₀.mul_mem hvB hb
  have hτ2 : τ * τ = 1 := by
    ext u
    rw [MulAut.mul_apply]
    rcases hτv u with h | h
    · rw [mul_inv_eq_one.1 h, mul_inv_eq_one.1 h]; rfl
    · have h1 : τ u = v * u := mul_inv_eq_iff_eq_mul.1 h
      rw [h1, map_mul, hτv', h1, ← mul_assoc, hsq v, one_mul]; rfl
  have hτinv : τ⁻¹ = τ := (inv_eq_of_mul_eq_one_right hτ2)
  obtain ⟨k, hk7, hk⟩ := hYB (τ * s * τ⁻¹) (hτY s hsY) (fun b hb => by
    rw [hτinv, MulAut.mul_apply, MulAut.mul_apply]
    exact hτB _ (hsB _ (hτB b hb)))
  have hconj : ∀ i : ℕ, τ * s ^ i = s ^ (k * i) * τ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hτs : τ * s = s ^ k * τ := by
        calc τ * s = (τ * s * τ⁻¹) * τ := by group
          _ = s ^ k * τ := by rw [hk]
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, hτs, ← mul_assoc, ← pow_add, Nat.mul_succ]
  have hk2 : s ^ (k * k) = s := by
    have h1 : τ * s * τ⁻¹ = s ^ k := hk
    have h2 : τ * (s ^ k) * τ⁻¹ = s ^ (k * k) := by
      rw [hconj k, mul_assoc, mul_inv_cancel, mul_one]
    calc s ^ (k * k) = τ * (τ * s * τ⁻¹) * τ⁻¹ := by rw [h1, h2]
      _ = (τ * τ) * s * (τ * τ)⁻¹ := by group
      _ = s := by rw [hτ2]; group
  obtain ⟨w₀, hw₀B, hw₀1, hτw₀⟩ : ∃ w ∈ B₀, w ≠ 1 ∧ τ w = w := by
    let X := {b : V // b ∈ B₀ ∧ b ≠ 1}
    have hcardX : Fintype.card X = 7 := by
      have h1 : Fintype.card X = Fintype.card {b : B₀ // b ≠ 1} :=
        Fintype.card_congr ⟨fun b => ⟨⟨b.1, b.2.1⟩, fun h => b.2.2 (congrArg Subtype.val h)⟩,
          fun b => ⟨b.1.1, b.1.2, fun h => b.2 (Subtype.ext h)⟩, fun _ => rfl, fun _ => rfl⟩
      rw [h1, Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
        hB8]
    let f : Function.End X := fun b => ⟨τ b.1, hτB _ b.2.1, fun h => b.2.2
      (τ.injective (by rw [h, map_one]))⟩
    have hf2 : f ^ 2 ^ 1 = 1 := by
      funext b
      apply Subtype.ext
      show τ (τ b.1) = b.1
      rw [← MulAut.mul_apply, hτ2]; rfl
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf2
    rw [hcardX] at hmod
    have hpos : 0 < Fintype.card (Function.fixedPoints f) := by
      by_contra h0
      push Not at h0
      rw [Nat.le_zero.1 h0] at hmod
      exact absurd hmod (by decide)
    obtain ⟨⟨w, hw⟩⟩ := Fintype.card_pos_iff.1 hpos
    exact ⟨w.1, w.2.1, w.2.2, congrArg Subtype.val hw⟩
  have hsw₀ := hsfix w₀ hw₀B hw₀1
  have hpow_ne : ∀ m : ℕ, ¬ 7 ∣ m → (s ^ m) w₀ ≠ w₀ := fun m hm h =>
    hsw₀ (fix_of_pow_fix hs7 h hm)
  have hτpow : ∀ i : ℕ, τ ((s ^ i) w₀) = (s ^ (k * i)) w₀ := by
    intro i
    rw [← MulAut.mul_apply, hconj i, MulAut.mul_apply, hτw₀]
  have hk' : k = 1 ∨ k = 6 := by
    have h1 : (s ^ (k * k)) w₀ = (s ^ 1) w₀ := by rw [hk2, pow_one]
    have hkk : 1 ≤ k * k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso
        rw [h0, pow_zero] at hk
        apply hτ1
        have : s = 1 := by
          have := congrArg (fun z => τ⁻¹ * z * τ) hk
          simp only [mul_one, inv_mul_cancel] at this
          rw [← this]; group
        exact absurd (this ▸ hsw₀) (by simp)
      · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h0.ne' h0.ne')
    have h7 := seven_dvd_of_pow_apply_eq hs7 hsw₀ hkk h1
    interval_cases k <;> omega
  rcases hk' with rfl | rfl
  ·
    apply hτ1
    refine hid τ hτa fun b hb => ?_
    by_cases hb1 : b = 1
    · rw [hb1, map_one]
    obtain ⟨i, hi⟩ := hstrans w₀ hw₀B b hb hw₀1 hb1
    rw [← hi, hτpow i, one_mul]
  ·
    have hsapp : ∀ i j : ℕ, ∀ u, (s ^ i) ((s ^ j) u) = (s ^ (i + j)) u := by
      intro i j u; rw [pow_add, MulAut.mul_apply]
    have hsmod : ∀ m : ℕ, ∀ u, (s ^ m) u = (s ^ (m % 7)) u := by
      intro m u
      conv_lhs => rw [← Nat.mod_add_div m 7, pow_add, pow_mul, hs7, one_pow, mul_one]
    have hs1 : ∀ u, s u = (s ^ 1) u := fun u => by rw [pow_one]
    have hτs1 : τ (s w₀) = (s ^ 6) w₀ := by rw [hs1, hτpow 1]
    have hs61 : ∀ u, (s ^ 6) (s u) = u := by
      intro u
      have h67 : s ^ 6 * s = 1 := by rw [← pow_succ]; exact hs7
      rw [← MulAut.mul_apply, h67]; rfl
    have hprod1 : w₀ * s w₀ ≠ 1 := by
      intro h
      apply hsw₀
      rw [mul_eq_one_iff_eq_inv, hinvV] at h
      exact h.symm
    obtain ⟨j, hj⟩ := hstrans w₀ hw₀B (w₀ * s w₀) (B₀.mul_mem hw₀B (hsB _ hw₀B)) hw₀1 hprod1
    have hj7 : (s ^ (j % 7)) w₀ = w₀ * s w₀ := by rw [← hsmod]; exact hj
    set j' := j % 7 with hj'
    have hj'7 : j' < 7 := Nat.mod_lt _ (by norm_num)
    have e1 : (s ^ (6 * j')) w₀ = w₀ * (s ^ 6) w₀ := by
      have := congrArg τ hj7
      rwa [hτpow, map_mul, hτw₀, hτs1] at this
    have e2 : (s ^ (6 + j')) w₀ = (s ^ 6) w₀ * w₀ := by
      have := congrArg (fun u => (s ^ 6) u) hj7
      rwa [hsapp, map_mul, hs61] at this
    have e3 : (s ^ (6 * j')) w₀ = (s ^ (6 + j')) w₀ := by
      rw [e1, e2, hcomm]
    have hj4 : j' = 4 := by
      rcases le_total (6 + j') (6 * j') with hle | hle
      · have := seven_dvd_of_pow_apply_eq hs7 hsw₀ hle e3
        interval_cases j' <;> omega
      · have := seven_dvd_of_pow_apply_eq hs7 hsw₀ hle e3.symm
        interval_cases j' <;> omega
    rw [hj4] at hj7
    have f1 : w₀ * (s ^ 4) w₀ = s w₀ := by
      rw [hj7, ← mul_assoc, hsq, one_mul]
    have f2 : w₀ * (s ^ 3) w₀ = (s ^ 6) w₀ := by
      have := congrArg τ f1
      rw [map_mul, hτw₀, hτpow 4, hτs1, hsmod (6 * 4)] at this
      exact this
    have f4 : (s ^ 3) w₀ * w₀ = (s ^ 4) w₀ := by
      have := congrArg (fun u => (s ^ 3) u) f1
      rw [map_mul, hsapp, hs1 w₀, hsapp, hsmod (3 + 4)] at this
      exact this
    have f5 : (s ^ 6) w₀ = (s ^ 4) w₀ := by
      rw [← f2, hcomm, f4]
    have := seven_dvd_of_pow_apply_eq hs7 hsw₀ (by norm_num) f5
    omega

end Transvection


section Image

variable {A : Subgroup G}

omit [Finite G] in
theorem subgroupOf_inf' (H K L : Subgroup G) :
    (H ⊓ K).subgroupOf L = H.subgroupOf L ⊓ K.subgroupOf L := by
  ext x; simp [Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem card_subgroupOf_of_le {X L : Subgroup G} (h : X ≤ L) :
    Nat.card (X.subgroupOf L) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

omit [Finite G] in
theorem card_img_mul (M : Subgroup G) (hM : M ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ((M.subgroupOf (Subgroup.normalizer (A : Set G))).map A.normalizerMonoidHom) *
      Nat.card (M ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) = Nat.card M := by
  rw [← Subgroup.relIndex_ker]
  have h := Subgroup.relIndex_mul_card (H := A.normalizerMonoidHom.ker)
    (K := M.subgroupOf (Subgroup.normalizer (A : Set G)))
  rw [Subgroup.normalizerMonoidHom_ker, ← subgroupOf_inf',
    card_subgroupOf_of_le hM,
    card_subgroupOf_of_le (inf_le_right.trans hM), inf_comm] at h
  rw [Subgroup.normalizerMonoidHom_ker]
  exact h

omit [Finite G] in
theorem normalizerMonoidHom_apply (x : Subgroup.normalizer (A : Set G)) (a : A) :
    ((A.normalizerMonoidHom x a : A) : G) = (x : G) * a * (x : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe A x a

end Image

section SylowK

variable {A K : Subgroup G}

theorem exists_twoSubgroup_sz8
    (hA : IsElemAbelian 2 A) (hq : GorensteinWalter.IsQuasisimple K)
    (hcov : Nonempty (K ⧸ Subgroup.center K ≃* Sz 1))
    (hsup : A ⊓ K ⊔ A ⊓ Subgroup.centralizer (K : Set G) = A)
    (h56 : ((K ⊓ Subgroup.centralizer (A : Set G)).subgroupOf
      (K ⊓ Subgroup.normalizer (A : Set G))).index = 56) :
    ∃ P : Subgroup G, P ≤ K ⊓ Subgroup.normalizer (A : Set G) ∧
      8 ≤ Nat.card ((P.subgroupOf (Subgroup.normalizer (A : Set G))).map
        A.normalizerMonoidHom) ∧
      ∀ p ∈ P, ∀ u ∈ A, p * u * p⁻¹ * u⁻¹ ∈ A ⊓ K ⊓ Subgroup.centralizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set NA := Subgroup.normalizer (A : Set G) with hNA
  set N := K ⊓ NA with hN
  have hCN : K ⊓ Subgroup.centralizer (A : Set G) ≤ N :=
    inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow 2 N))
  set P := (P₀ : Subgroup N).map N.subtype with hP
  have hPN : P ≤ N := Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 P := P₀.2.map _
  refine ⟨P, hPN, ?_, ?_⟩
  ·
    set c := Nat.card (K ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) with hc
    have hcN : Nat.card N = 56 * c := by
      have := Subgroup.index_mul_card ((K ⊓ Subgroup.centralizer (A : Set G)).subgroupOf N)
      rw [h56, card_subgroupOf_of_le hCN] at this
      exact this.symm
    have hc0 : c ≠ 0 := Nat.card_pos.ne'
    have hcardP : Nat.card P = 2 ^ (c.factorization 2 + 3) := by
      rw [hP, Subgroup.card_map_of_injective N.subtype_injective, Sylow.card_eq_multiplicity,
        hcN, Nat.factorization_mul (by norm_num) hc0]
      have h56f : (56 : ℕ).factorization 2 = 3 := by
        rw [show (56 : ℕ) = 2 ^ 3 * 7 by norm_num, Nat.factorization_mul (by norm_num)
          (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
        simp [Nat.factorization_eq_zero_of_not_dvd]
      rw [Finsupp.add_apply, h56f, add_comm]
    have hPC : P ⊓ Subgroup.centralizer (A : Set G) ≤ K ⊓ Subgroup.centralizer (A : Set G) :=
      inf_le_inf_right _ (hPN.trans inf_le_left)
    obtain ⟨b, hb⟩ := (hP2.to_le (inf_le_left :
      P ⊓ Subgroup.centralizer (A : Set G) ≤ P)).exists_card_eq
    have hbc : b ≤ c.factorization 2 := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hc0, ← hb]
      exact Subgroup.card_dvd_of_le hPC
    have hmul := card_img_mul P (hPN.trans inf_le_right)
    rw [hcardP, hb] at hmul
    by_contra hlt
    push Not at hlt
    have h1 : 2 ^ b ≤ 2 ^ c.factorization 2 := Nat.pow_le_pow_right (by norm_num) hbc
    have h2 : Nat.card ((P.subgroupOf NA).map A.normalizerMonoidHom) * 2 ^ b < 8 * 2 ^ b :=
      Nat.mul_lt_mul_of_pos_right hlt (by positivity)
    have h3 : 2 ^ (c.factorization 2 + 3) = 8 * 2 ^ c.factorization 2 := by
      rw [pow_add]; ring
    have h4 : 8 * 2 ^ b ≤ 8 * 2 ^ c.factorization 2 := Nat.mul_le_mul_left 8 h1
    exact absurd (lt_of_lt_of_le h2 (h4.trans (h3.symm.trans hmul.symm).le)) (lt_irrefl _)
  ·
    intro p hp u hu
    have hcomm : ∀ x ∈ A ⊓ K, ∀ z ∈ A ⊓ Subgroup.centralizer (K : Set G), x * z = z * x :=
      fun x hx z hz => congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx.1⟩ ⟨z, hz.1⟩)
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).2
    rw [hsup] at hset
    have hu' : u ∈ ((A ⊓ K : Subgroup G) : Set G) * ((A ⊓ Subgroup.centralizer (K : Set G) :
        Subgroup G) : Set G) := by rw [← hset]; exact hu
    obtain ⟨u₁, hu₁, w, hw, rfl⟩ := hu'
    have hpK : p ∈ K := (hPN hp).1
    have hpA : p ∈ NA := (hPN hp).2
    have hAK2 : IsPGroup 2 (A ⊓ K : Subgroup G) := (isPGroup_of_isElemAbelian hA).to_le inf_le_left
    have hPnorm : P ≤ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨(hPN hx).2, Subgroup.le_normalizer (hPN hx).1⟩
    have hT2 := hP2.to_sup_of_normal_right' hAK2 hPnorm
    have hTK : P ⊔ A ⊓ K ≤ K := sup_le (hPN.trans inf_le_left) inf_le_right
    have hu₁2 : u₁ ^ 2 = 1 := hA.2 u₁ hu₁.1
    have hkey := commutator_mem_centralizer_of_sz8 hq hcov hTK hT2
      (Subgroup.mem_sup_right hu₁) hu₁2 (Subgroup.mem_sup_left (P.inv_mem hp))
    rw [inv_inv] at hkey
    have hwp : p * w = w * p := Subgroup.mem_centralizer_iff.1 hw.2 p hpK
    have heq : p * (u₁ * w) * p⁻¹ * (u₁ * w)⁻¹ = p * u₁ * p⁻¹ * u₁⁻¹ := by
      calc p * (u₁ * w) * p⁻¹ * (u₁ * w)⁻¹ = p * u₁ * (w * p⁻¹) * w⁻¹ * u₁⁻¹ := by group
        _ = p * u₁ * (p⁻¹ * w) * w⁻¹ * u₁⁻¹ := by
          rw [show w * p⁻¹ = p⁻¹ * w from by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hwp, inv_mul_cancel_left]]
        _ = p * u₁ * p⁻¹ * u₁⁻¹ := by group
    rw [heq]
    refine ⟨⟨?_, ?_⟩, hkey⟩
    · have h1 : p * u₁ * p⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hpA u₁).1 hu₁.1
      exact A.mul_mem h1 (A.inv_mem hu₁.1)
    · exact K.mul_mem (K.mul_mem (K.mul_mem hpK hu₁.2) (K.inv_mem hpK)) (K.inv_mem hu₁.2)

end SylowK



section Semiregular

variable {A : Subgroup G}

theorem false_of_sz8Cover_semiregular (h210 : S_G210) (hA : IsElemAbelian 2 A) {K : Subgroup G}
    {y : G} (hON : ONanHyp A (Subgroup.normalizer (A : Set G)) y)
    (hSR : ∀ x ∈ Subgroup.normalizer (A : Set G),
      conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G)) ≠
        A ⊓ Subgroup.centralizer ({y} : Set G) → ∀ k : ℕ,
      conjSub (y ^ k) (conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G))) =
        conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G)) →
      y ^ k ∈ Subgroup.centralizer (A : Set G))
    (hWne : A ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥)
    (hnormK : ∀ x ∈ Subgroup.normalizer (A : Set G),
      conjSub x (A ⊓ Subgroup.centralizer (K : Set G)) = A ⊓ Subgroup.centralizer (K : Set G) →
      x ∈ Subgroup.normalizer (K : Set G))
    (hyK : y ∈ K) (hyN : y ∈ Subgroup.normalizer (A : Set G)) (hyodd : Odd (orderOf y))
    (hytrans : ∀ b ∈ ⁅A, Subgroup.zpowers y⁆, ∀ c ∈ ⁅A, Subgroup.zpowers y⁆, b ≠ 1 → c ≠ 1 →
      ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c)
    (hyC : A ⊓ Subgroup.centralizer ({y} : Set G) = A ⊓ Subgroup.centralizer (K : Set G))
    (hy7 : y ^ 7 ∈ Subgroup.centralizer (A : Set G))
    (hB8 : Nat.card (⁅A, Subgroup.zpowers y⁆ : Subgroup G) = 8)
    (hWB : A ⊓ Subgroup.centralizer (K : Set G) ⊓ ⁅A, Subgroup.zpowers y⁆ = ⊥)
    (hdec : A ⊓ Subgroup.centralizer (K : Set G) ⊔ ⁅A, Subgroup.zpowers y⁆ = A)
    {P : Subgroup G} (hPN : P ≤ K ⊓ Subgroup.normalizer (A : Set G))
    (hP8 : 8 ≤ Nat.card ((P.subgroupOf (Subgroup.normalizer (A : Set G))).map
      A.normalizerMonoidHom))
    (hPZ : ∀ p ∈ P, ∀ u ∈ A, p * u * p⁻¹ * u⁻¹ ∈ A ⊓ K ⊓ Subgroup.centralizer (K : Set G))
    (h56 : ((K ⊓ Subgroup.centralizer (A : Set G)).subgroupOf
      (K ⊓ Subgroup.normalizer (A : Set G))).index = 56) : False := by
  classical
  set NA := Subgroup.normalizer (A : Set G) with hNA
  set W := A ⊓ Subgroup.centralizer (K : Set G) with hW
  set B₀ := ⁅A, Subgroup.zpowers y⁆ with hB₀
  set φ := A.normalizerMonoidHom with hφ
  have hB₀A : B₀ ≤ A := commutator_zpowers_le_self hyN
  have hyB₀ := mem_normalizer_commutator hyN
  have hdisj : B₀ ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ :=
    commutator_inf_centralizer_eq_bot hA hyN hyodd
  obtain ⟨hW2, htransA⟩ := h210 G A NA y hON hSR
  rw [hyC] at hW2
  obtain ⟨⟨a₀, ha₀W⟩, ha₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hWne
  have ha₀1' : a₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
  have hWa : ∀ w ∈ W, w = 1 ∨ w = a₀ := by
    intro w hw
    by_contra h
    push Not at h
    obtain ⟨u, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : W)).1 hW2
    have h1 := huniq ⟨a₀, ha₀W⟩ (fun h' => ha₀1' (congrArg Subtype.val h'))
    have h2 := huniq ⟨w, hw⟩ (fun h' => h.1 (congrArg Subtype.val h'))
    exact h.2 (congrArg Subtype.val (h2.trans h1.symm))
  have hPW : ∀ p ∈ P, ∀ u ∈ A, p * u * p⁻¹ * u⁻¹ = 1 ∨ p * u * p⁻¹ * u⁻¹ = a₀ :=
    fun p hp u hu => hWa _ ⟨(hPZ p hp u hu).1.1, (hPZ p hp u hu).2⟩
  have hB₀ne : B₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB8
    omega
  obtain ⟨⟨v, hvB⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB₀ne
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  obtain ⟨g, hgA, hg⟩ := htransA a₀ ha₀W.1 v (hB₀A hvB) ha₀1' hv1'
  set Pg := conjSub g P with hPg
  have hNAg : conjSub g NA = NA := conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hgA)
  have hPgN : Pg ≤ NA := by
    have : conjSub g P ≤ conjSub g NA := Subgroup.map_mono (hPN.trans inf_le_right)
    rwa [hNAg] at this
  have hPgv : ∀ r ∈ Pg, ∀ u ∈ A, r * u * r⁻¹ * u⁻¹ = 1 ∨ r * u * r⁻¹ * u⁻¹ = v := by
    intro r hr u hu
    have hp : g * r * g⁻¹ ∈ P := mem_conjSub.1 hr
    have hu' : g * u * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hgA u).1 hu
    have heq : r * u * r⁻¹ * u⁻¹ = g⁻¹ * ((g * r * g⁻¹) * (g * u * g⁻¹) * (g * r * g⁻¹)⁻¹ *
        (g * u * g⁻¹)⁻¹) * g := by group
    rcases hPW _ hp _ hu' with h | h
    · left; rw [heq, h]; group
    · right; rw [heq, h, hg]
  have hCAg : conjSub g (Subgroup.centralizer (A : Set G)) = Subgroup.centralizer (A : Set G) := by
    rw [conjSub_centralizer, conjSub_eq_of_mem_normalizer hgA]
  have hcardPg : 8 ≤ Nat.card ((Pg.subgroupOf NA).map φ) := by
    have h1 := card_img_mul P (hPN.trans inf_le_right)
    have h2 := card_img_mul Pg hPgN
    have h3 : Nat.card (Pg ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) =
        Nat.card (P ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
      have : Pg ⊓ Subgroup.centralizer (A : Set G) =
          conjSub g (P ⊓ Subgroup.centralizer (A : Set G)) := by
        rw [hPg]
        unfold conjSub
        rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective]
        have := hCAg
        unfold conjSub at this
        rw [this]
      rw [this, card_conjSub]
    have h4 : Nat.card Pg = Nat.card P := card_conjSub g P
    rw [h3, h4, ← h1] at h2
    have hpos : 0 < Nat.card (P ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := Nat.card_pos
    rw [Nat.eq_of_mul_eq_mul_right hpos h2]
    exact hP8
  obtain ⟨t, htPg, htA, hta₀⟩ : ∃ t ∈ Pg, t ∉ Subgroup.centralizer (A : Set G) ∧
      t * a₀ * t⁻¹ = a₀ := by
    obtain ⟨σ₁, σ₂, h1, h2, h12⟩ :=
      CFSG.Walter.exists_ne_one_ne_of_three_le_card (H := ((Pg.subgroupOf NA).map φ))
        (by omega)
    obtain ⟨⟨r₁, hr₁N⟩, hr₁, hσ₁⟩ := σ₁.2
    obtain ⟨⟨r₂, hr₂N⟩, hr₂, hσ₂⟩ := σ₂.2
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hr₁ hr₂
    have hnot : ∀ (r : G) (hrN : r ∈ NA), φ ⟨r, hrN⟩ ≠ 1 →
        r ∉ Subgroup.centralizer (A : Set G) := by
      intro r hrN hne hrC
      apply hne
      have : (⟨r, hrN⟩ : NA) ∈ φ.ker := by
        rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]; exact hrC
      exact this
    have hφ1 : φ ⟨r₁, hr₁N⟩ ≠ 1 := fun h => h1 (Subtype.ext (by rw [← hσ₁, h]; rfl))
    have hφ2 : φ ⟨r₂, hr₂N⟩ ≠ 1 := fun h => h2 (Subtype.ext (by rw [← hσ₂, h]; rfl))
    have hφ12 : φ ⟨r₁, hr₁N⟩ ≠ φ ⟨r₂, hr₂N⟩ := fun h => h12 (Subtype.ext (by rw [← hσ₁, ← hσ₂, h]))
    by_cases hc1 : r₁ * a₀ * r₁⁻¹ = a₀
    · exact ⟨r₁, hr₁, hnot r₁ hr₁N hφ1, hc1⟩
    by_cases hc2 : r₂ * a₀ * r₂⁻¹ = a₀
    · exact ⟨r₂, hr₂, hnot r₂ hr₂N hφ2, hc2⟩
    have e1 : r₁ * a₀ * r₁⁻¹ = v * a₀ := by
      rcases hPgv r₁ hr₁ a₀ ha₀W.1 with h | h
      · exact absurd (mul_inv_eq_one.1 h) hc1
      · exact mul_inv_eq_iff_eq_mul.1 h
    have e2 : r₂ * a₀ * r₂⁻¹ = v * a₀ := by
      rcases hPgv r₂ hr₂ a₀ ha₀W.1 with h | h
      · exact absurd (mul_inv_eq_one.1 h) hc2
      · exact mul_inv_eq_iff_eq_mul.1 h
    refine ⟨r₁⁻¹ * r₂, Pg.mul_mem (Pg.inv_mem hr₁) hr₂, ?_, ?_⟩
    · refine hnot _ (NA.mul_mem (NA.inv_mem hr₁N) hr₂N) ?_
      intro h
      apply hφ12
      have : (φ ⟨r₁, hr₁N⟩)⁻¹ * φ ⟨r₂, hr₂N⟩ = 1 := by
        rw [← map_inv, ← map_mul]; exact h
      rw [inv_mul_eq_one] at this
      exact this
    · calc r₁⁻¹ * r₂ * a₀ * (r₁⁻¹ * r₂)⁻¹ = r₁⁻¹ * (r₂ * a₀ * r₂⁻¹) * r₁ := by group
        _ = r₁⁻¹ * (r₁ * a₀ * r₁⁻¹) * r₁ := by rw [e2, e1]
        _ = a₀ := by group
  have htN : t ∈ NA := hPgN htPg
  have htW : conjSub t W = W := by
    refine conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hWa w hw with rfl | rfl
    · simp
    · calc w * t = t * (t⁻¹ * w * t) := by group
        _ = t * w := by
          congr 1
          calc t⁻¹ * w * t = t⁻¹ * (t * w * t⁻¹) * t := by rw [hta₀]
            _ = w := by group
  have htK := hnormK t htN htW
  have hsqV : ∀ u : A, u * u = 1 := fun u => Subtype.ext (by simpa [sq] using hA.2 u u.2)
  have hcommWB : ∀ w ∈ W, ∀ c ∈ B₀, w * c = c * w := fun w hw c hc =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨w, hw.1⟩ ⟨c, hB₀A hc⟩)
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute W B₀ hcommWB).2
  rw [hdec] at hset
  have hφapp : ∀ (x : NA) (u : A), ((φ x u : A) : G) = (x : G) * u * (x : G)⁻¹ :=
    fun x u => normalizerMonoidHom_apply x u
  refine false_of_transvection (V := A) (fun u w => hA.1.is_comm.comm u w) hsqV
    (a₀ := ⟨a₀, ha₀W.1⟩) (B₀ := B₀.subgroupOf A) ?_ ?_ ?_ (s := φ ⟨y, hyN⟩) ?_ ?_ ?_ ?_
    (Y := ((K ⊓ NA).subgroupOf NA).map φ) ?_ ?_ (Q := (P.subgroupOf NA).map φ) ?_ hP8 ?_ ?_
    (τ := φ ⟨t, htN⟩) ?_ ?_ (v := ⟨v, hB₀A hvB⟩) ?_ ?_ ?_ ?_
  ·
    intro h
    rw [Subgroup.mem_subgroupOf] at h
    have : a₀ ∈ W ⊓ B₀ := ⟨ha₀W, h⟩
    rw [hWB] at this
    exact ha₀1' this
  ·
    intro u
    have hu : (u : G) ∈ (W : Set G) * (B₀ : Set G) := by
      rw [← hset]; exact u.2
    obtain ⟨w, hw, c, hc, hwc⟩ := Set.mem_mul.1 hu
    rcases hWa w hw with rfl | rfl
    · left
      rw [Subgroup.mem_subgroupOf, ← hwc, one_mul]; exact hc
    · right
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, ← hwc, ← mul_assoc]
      have : w * w = 1 := by simpa [sq] using hA.2 w hw.1
      rw [this, one_mul]; exact hc
  · rw [card_subgroupOf_of_le hB₀A]; exact hB8
  ·
    intro b hb
    rw [Subgroup.mem_subgroupOf] at hb ⊢
    rw [hφapp]
    exact (Subgroup.mem_normalizer_iff.1 hyB₀ b).1 hb
  ·
    rw [← map_pow]
    have : (⟨y, hyN⟩ : NA) ^ 7 ∈ φ.ker := by
      rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      simpa using hy7
    exact this
  ·
    intro b hb c hc hb1 hc1
    rw [Subgroup.mem_subgroupOf] at hb hc
    obtain ⟨k, hk⟩ := hytrans c hc b hb (fun h => hc1 (Subtype.ext h))
      (fun h => hb1 (Subtype.ext h))
    refine ⟨k, Subtype.ext ?_⟩
    rw [← map_pow, hφapp]
    simp only [SubgroupClass.coe_pow]
    rw [← hk]
    group
  ·
    intro b hb hb1 h
    rw [Subgroup.mem_subgroupOf] at hb
    have h' := congrArg Subtype.val h
    rw [hφapp] at h'
    have hbC : (b : G) ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (b : G) * y = y * b * y⁻¹ * y := by rw [h']
        _ = y * b := by group
    have : (b : G) ∈ B₀ ⊓ Subgroup.centralizer ({y} : Set G) := ⟨hb, hbC⟩
    rw [hdisj] at this
    exact hb1 (Subtype.ext this)
  ·
    have h1 := card_img_mul (K ⊓ NA) inf_le_right
    have h2 : K ⊓ NA ⊓ Subgroup.centralizer (A : Set G) = K ⊓ Subgroup.centralizer (A : Set G) := by
      rw [inf_assoc, inf_of_le_right (Subgroup.centralizer_le_normalizer _)]
    have h3 := Subgroup.index_mul_card ((K ⊓ Subgroup.centralizer (A : Set G)).subgroupOf (K ⊓ NA))
    rw [h56, card_subgroupOf_of_le (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))]
      at h3
    rw [h2, ← h3] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  · exact ⟨⟨y, hyN⟩, by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact ⟨hyK, hyN⟩, rfl⟩
  · exact Subgroup.map_mono fun x hx => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢; exact hPN hx
  ·
    rintro σ ⟨⟨p, hpN⟩, hp, rfl⟩ u
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hp
    rcases hPW p hp u u.2 with h | h
    · left; apply Subtype.ext; rw [Subgroup.coe_mul, hφapp]; simpa using h
    · right; apply Subtype.ext; rw [Subgroup.coe_mul, hφapp]; simpa using h
  ·
    rintro σ ⟨⟨n, hnN⟩, hn, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hn
    apply Subtype.ext
    rw [hφapp]
    have := Subgroup.mem_centralizer_iff.1 ha₀W.2 n hn.1
    simp only
    rw [this]; group
  ·
    intro h
    apply htA
    have : (⟨t, htN⟩ : NA) ∈ φ.ker := h
    rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at this
    exact this
  ·
    apply Subtype.ext
    rw [hφapp]
    exact hta₀
  · rw [Subgroup.mem_subgroupOf]; exact hvB
  · exact fun h => hv1' (congrArg Subtype.val h)
  ·
    intro u
    rcases hPgv t htPg u u.2 with h | h
    · left; apply Subtype.ext; rw [Subgroup.coe_mul, hφapp]; simpa using h
    · right; apply Subtype.ext; rw [Subgroup.coe_mul, hφapp]; simpa using h
  ·
    rintro σ ⟨⟨n, hnN⟩, hn, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hn
    refine ⟨⟨t, htN⟩ * ⟨n, hnN⟩ * ⟨t, htN⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    refine ⟨?_, NA.mul_mem (NA.mul_mem htN hnN) (NA.inv_mem htN)⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 htK n).1 hn.1

end Semiregular

section Main

variable {A : Subgroup G}

theorem false_of_sz8Cover
    (h210 : S_G210) (hmult : S_GSz8Mult) (hA : IsElemAbelian 2 A)
    {H K : Subgroup G} (hK : GorensteinWalter.IsComponentOf K (normalClosureIn H A))
    (h2 : 2 ≤ Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G))
    (hTI : ∀ x ∈ Subgroup.normalizer (A : Set G),
      conjSub x (A ⊓ Subgroup.centralizer (K : Set G)) ≠ A ⊓ Subgroup.centralizer (K : Set G) →
      A ⊓ Subgroup.centralizer (K : Set G) ⊓
        conjSub x (A ⊓ Subgroup.centralizer (K : Set G)) = ⊥)
    (hnormK : ∀ x ∈ Subgroup.normalizer (A : Set G),
      conjSub x (A ⊓ Subgroup.centralizer (K : Set G)) = A ⊓ Subgroup.centralizer (K : Set G) →
      x ∈ Subgroup.normalizer (K : Set G))
    (hsup : A ⊓ K ⊔ A ⊓ Subgroup.centralizer (K : Set G) = A)
    {y : G} (hyK : y ∈ K) (hyN : y ∈ Subgroup.normalizer (A : Set G)) (hyodd : Odd (orderOf y))
    (hytrans : ∀ b ∈ ⁅A, Subgroup.zpowers y⁆, ∀ c ∈ ⁅A, Subgroup.zpowers y⁆, b ≠ 1 → c ≠ 1 →
      ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c)
    (hyC : A ⊓ Subgroup.centralizer ({y} : Set G) = A ⊓ Subgroup.centralizer (K : Set G))
    (hON : ONanHyp A (Subgroup.normalizer (A : Set G)) y) (hcov : IsGoldSz8Cover K)
    (h56 : ((K ⊓ Subgroup.centralizer (A : Set G)).subgroupOf
      (K ⊓ Subgroup.normalizer (A : Set G))).index = 56)
    (hAy : y ∉ Subgroup.centralizer (A : Set G)) (hy7 : y ^ 7 ∈ Subgroup.centralizer (A : Set G)) :
    False := by
  classical
  set NA := Subgroup.normalizer (A : Set G) with hNA
  set W := A ⊓ Subgroup.centralizer (K : Set G) with hW
  set B₀ := ⁅A, Subgroup.zpowers y⁆ with hB₀
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h2
    omega
  have hB8 := card_commutator_eq_eight hA hyN hyodd hAy hy7 hytrans
  have hB₀A : B₀ ≤ A := commutator_zpowers_le_self hyN
  have hdisj : B₀ ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ :=
    commutator_inf_centralizer_eq_bot hA hyN hyodd
  have hWB : W ⊓ B₀ = ⊥ := by
    rw [eq_bot_iff, ← hdisj, ← hyC]
    exact fun z hz => ⟨hz.2, hz.1.2⟩
  have hdec : W ⊔ B₀ = A := by
    have := (coprime_decomp hA hyN hyodd).1
    rwa [hyC] at this
  have hyB₀ := mem_normalizer_commutator hyN
  obtain ⟨P, hPN, hP8, hPZ⟩ := exists_twoSubgroup_sz8 hA hK.2.2 hcov.1 hsup h56
  set Z₀ := A ⊓ K ⊓ Subgroup.centralizer (K : Set G) with hZ₀
  have hZ₀W : Z₀ ≤ W := fun z hz => ⟨hz.1.1, hz.2⟩
  have hZ₀ne : Z₀ ≠ ⊥ := by
    intro hZ
    have hPC : ∀ p ∈ P, p ∈ Subgroup.centralizer (A : Set G) := by
      intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h := hPZ p hp u hu
      rw [hZ, Subgroup.mem_bot] at h
      have : p * u * p⁻¹ = u := by
        rw [mul_inv_eq_one] at h; exact h
      calc u * p = p * u * p⁻¹ * p := by rw [this]
        _ = p * u := by group
    have hbot : (P.subgroupOf NA).map A.normalizerMonoidHom = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, Subgroup.normalizerMonoidHom_ker]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hPC _ hx
    rw [hbot, Subgroup.card_bot] at hP8
    omega
  have hZcard : Nat.card Z₀ ≤ 4 := by
    have hq' : CFSG.Open.IsQuasisimple K := ⟨hK.2.2.2.1, hK.2.2.2.2⟩
    refine le_trans ?_ (hmult K hq' hcov.1)
    refine Nat.card_le_card_of_injective (fun z : Z₀ => (⟨⟨z.1, z.2.1.2⟩,
      Subgroup.mem_center_iff.2 fun k => Subtype.ext ?_⟩ : Subgroup.center K)) ?_
    · exact (Subgroup.mem_centralizer_iff.1 z.2.2 k k.2)
    · intro z₁ z₂ h
      exact Subtype.ext (congrArg (fun c : Subgroup.center K => ((c : K) : G)) h)
  by_cases hSR : ∀ x ∈ NA, conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G)) ≠
      A ⊓ Subgroup.centralizer ({y} : Set G) → ∀ k : ℕ,
      conjSub (y ^ k) (conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G))) =
        conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G)) →
      y ^ k ∈ Subgroup.centralizer (A : Set G)
  · exact false_of_sz8Cover_semiregular h210 hA hON hSR hWne hnormK hyK hyN hyodd hytrans
      hyC hy7 hB8 hWB hdec hPN hP8 hPZ h56
  ·
    push Not at hSR
    obtain ⟨x, hx, hne, k, hk, hyk⟩ := hSR
    rw [hyC] at hne hk
    set B := conjSub x W with hBdef
    have hBW : W ⊓ B = ⊥ := hTI x hx hne
    have hBA : B ≤ A := by
      have : conjSub x W ≤ conjSub x A := Subgroup.map_mono inf_le_left
      rwa [conjSub_eq_of_mem_normalizer hx] at this
    have hk7 : ¬ 7 ∣ k := by
      rintro ⟨m, rfl⟩
      apply hyk
      rw [pow_mul]
      exact Subgroup.pow_mem _ hy7 m
    have hyB : y ∈ Subgroup.normalizer (B : Set G) := by
      have h1 : y ^ k ∈ Subgroup.normalizer (B : Set G) := mem_normalizer_of_conjSub_eq hk
      have h2 : y ^ 7 ∈ Subgroup.normalizer (B : Set G) :=
        Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le (by exact_mod_cast hBA) hy7)
      exact mem_of_pow_mem_of_pow_seven_mem h1 h2 hk7
    have hBcomm : IsMulCommutative B := ⟨⟨fun a b => by
      apply Subtype.ext
      have := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, hBA a.2⟩ ⟨b, hBA b.2⟩)
      simpa using this⟩⟩
    have hBelem : IsElemAbelian 2 B := ⟨hBcomm, fun b hb => hA.2 b (hBA hb)⟩
    have hBB₀ : B ≤ B₀ := by
      have hdecB := (coprime_decomp hBelem hyB hyodd).1
      rw [← hdecB]
      refine sup_le ?_ (Subgroup.commutator_mono hBA le_rfl)
      intro b hb
      have hbW : b ∈ W := by
        rw [← hyC]; exact ⟨hBA hb.1, hb.2⟩
      have : b ∈ W ⊓ B := ⟨hbW, hb.1⟩
      rw [hBW] at this
      rw [Subgroup.mem_bot.1 this]
      exact B₀.one_mem
    have hcardB : Nat.card B = Nat.card W := card_conjSub x W
    have hBne : B ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hcardB
      omega
    have hB₀B : B₀ ≤ B := by
      obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBne
      have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
      intro c hc
      by_cases hc1 : c = 1
      · rw [hc1]; exact B.one_mem
      obtain ⟨j, hj⟩ := hytrans b (hBB₀ hb) c hc hb1' hc1
      rw [← hj]
      exact pow_conj_mem hyB j hb
    have hW8 : Nat.card W = 8 := by rw [← hcardB, le_antisymm hBB₀ hB₀B, hB8]
    have hy'A : x * y * x⁻¹ ∈ NA := NA.mul_mem (NA.mul_mem hx hyN) (NA.inv_mem hx)
    have hy'W : conjSub (x * y * x⁻¹) W = W := by
      rw [conjSub_mul, conjSub_mul, ← hBdef, conjSub_eq_of_mem_normalizer hyB, hBdef,
        ← conjSub_mul, mul_inv_cancel, conjSub_one]
    have hy'K := hnormK _ hy'A hy'W
    have hy'Z : x * y * x⁻¹ ∈ Subgroup.normalizer (Z₀ : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hy'A, hy'K⟩, GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup K hy'K⟩
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ₀ne
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    obtain ⟨w, hwW, hwZ⟩ : ∃ w ∈ W, w ∉ Z₀ := by
      by_contra h
      push Not at h
      have := Subgroup.card_le_of_le (show W ≤ Z₀ from h)
      omega
    have hw1 : w ≠ 1 := fun h => hwZ (h ▸ Z₀.one_mem)
    have hconj1 : ∀ u : G, u ≠ 1 → x⁻¹ * u * x ≠ 1 := by
      intro u hu h
      apply hu
      calc u = x * (x⁻¹ * u * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group
    obtain ⟨j, hj⟩ := hytrans _ (hBB₀ (conj_mem_conjSub (hZ₀W hz))) _
      (hBB₀ (conj_mem_conjSub hwW)) (hconj1 z hz1') (hconj1 w hw1)
    have hconj : ((x * y * x⁻¹) ^ j)⁻¹ * z * (x * y * x⁻¹) ^ j = w := by
      rw [conj_pow]
      calc (x * y ^ j * x⁻¹)⁻¹ * z * (x * y ^ j * x⁻¹)
          = x * ((y ^ j)⁻¹ * (x⁻¹ * z * x) * y ^ j) * x⁻¹ := by group
        _ = x * (x⁻¹ * w * x) * x⁻¹ := by rw [hj]
        _ = w := by group
    have := pow_conj_mem hy'Z j hz
    rw [hconj] at this
    exact hwZ this

end Main

end CFSG.Goldschmidt.G75
