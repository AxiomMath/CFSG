module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2PGL
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AutAlternatingFour

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.GorensteinWalter
open scoped Pointwise

universe u

theorem perm_four_eq_one_of_commute_three : ∀ σ : Equiv.Perm (Fin 4), σ ^ 2 = 1 →
    ∀ a : alternatingGroup (Fin 4), a ^ 3 = 1 → a ≠ 1 →
      σ * (a : Equiv.Perm (Fin 4)) * σ⁻¹ = a → σ = 1 := by
  decide

theorem perm_five_eq_one_of_commute_five : ∀ σ : Equiv.Perm (Fin 5), σ ^ 2 = 1 →
    ∀ a : alternatingGroup (Fin 5), a ^ 5 = 1 → a ≠ 1 →
      σ * (a : Equiv.Perm (Fin 5)) * σ⁻¹ = a → σ = 1 := by
  decide +kernel

theorem alternating_four_not_inverted : ∀ t x : alternatingGroup (Fin 4), x ^ 3 = 1 →
    x ≠ 1 → t * x * t⁻¹ ≠ x⁻¹ := by
  decide

theorem perm_four_sign_of_pow_three : ∀ x : Equiv.Perm (Fin 4), x ^ 3 = 1 →
    Equiv.Perm.sign x = 1 := by
  decide

theorem mulAut_eq_of_alternating {N : Type*} [Group N] {n : ℕ}
    (e : N ≃* alternatingGroup (Fin n))
    (hc : Function.Bijective (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
      Equiv.Perm (Fin n) →* MulAut (alternatingGroup (Fin n))))
    (P : alternatingGroup (Fin n) → Prop)
    (hD : ∀ σ : Equiv.Perm (Fin n), σ ^ 2 = 1 → ∀ a : alternatingGroup (Fin n), P a →
      σ * (a : Equiv.Perm (Fin n)) * σ⁻¹ = a → σ = 1)
    (α : MulAut N) (hα : ∀ x, α (α x) = x) (y : N) (hy : α y = y) (hPy : P (e y)) :
    ∀ x, α x = x := by
  let α' : MulAut (alternatingGroup (Fin n)) := MulAut.congr e α
  have hα' : ∀ a, α' a = e (α (e.symm a)) := fun a => rfl
  obtain ⟨σ, hσ⟩ := hc.2 α'
  have hσ2 : σ ^ 2 = 1 := by
    apply hc.1
    rw [map_pow, hσ, map_one]
    ext a
    simp [pow_two, hα', hα]
  have hfix : σ * (e y : Equiv.Perm (Fin n)) * σ⁻¹ = e y := by
    have h1 : MulAut.conjNormal σ (e y) = e y := by
      rw [hσ, hα', MulEquiv.symm_apply_apply, hy]
    have h2 := congrArg Subtype.val h1
    rwa [MulAut.conjNormal_apply] at h2
  have hσ1 := hD σ hσ2 (e y) hPy hfix
  intro x
  have h1 : α' (e x) = e x := by
    rw [← hσ, hσ1, map_one]
    rfl
  rw [hα', MulEquiv.symm_apply_apply] at h1
  exact e.injective h1

@[expose] def restrictMulAut {G : Type*} [Group G] (φ : MulAut G) (M : Subgroup G)
    (h : ∀ x, x ∈ M ↔ φ x ∈ M) : MulAut M where
  toFun x := ⟨φ x, (h x).mp x.2⟩
  invFun x := ⟨φ.symm x, (h _).mpr (by simp)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp

theorem restrictMulAut_apply {G : Type*} [Group G] (φ : MulAut G) (M : Subgroup G)
    (h : ∀ x, x ∈ M ↔ φ x ∈ M) (x : M) : (restrictMulAut φ M h x : G) = φ x := rfl

theorem card_eq_two_mul_card_comap {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {H : Subgroup (PGL2 K)}
    {g : PGL2 K} (hgH : g ∈ H) (hgJ : g ∉ pslRange K) :
    Nat.card H = 2 * Nat.card (H.comap
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K))) := by
  let toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)
  have hinj : Function.Injective toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have : (pslRange K).Normal := pslRange_normal hK hcard
  have hJ2 := pslRange_index_eq_two hK
  have h1 : Nat.card (H.comap toPGL) = Nat.card (pslRange K ⊓ H : Subgroup (PGL2 K)) := by
    rw [Nat.card_congr ((H.comap toPGL).equivMapOfInjective toPGL hinj).toEquiv,
      Subgroup.map_comap_eq]
  have hdvd : (pslRange K).relIndex H ∣ 2 := by
    have := Subgroup.relIndex_dvd_index_of_normal (pslRange K) H
    rwa [hJ2] at this
  have hrel : (pslRange K).relIndex H = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd ((Subgroup.relIndex_eq_one.mp h) hgH) hgJ
    · exact h
  have h2 := ((pslRange K).subgroupOf H).card_mul_index
  have hrel' : ((pslRange K).subgroupOf H).index = 2 := hrel
  rw [hrel'] at h2
  have h3 : Nat.card ((pslRange K).subgroupOf H) =
      Nat.card (pslRange K ⊓ H : Subgroup (PGL2 K)) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  change Nat.card H = 2 * Nat.card (H.comap toPGL)
  rw [h1, ← h3]
  omega

theorem not_inverted_of_equiv_alternating_four {M : Type*} [Group M]
    (e : M ≃* alternatingGroup (Fin 4)) {y t : M} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hinv : t * y * t⁻¹ = y⁻¹) : False := by
  have key : e t * e y * (e t)⁻¹ = (e y)⁻¹ := by
    calc e t * e y * (e t)⁻¹ = e (t * y * t⁻¹) := by simp only [map_mul, map_inv]
      _ = (e y)⁻¹ := by rw [hinv, map_inv]
  exact alternating_four_not_inverted (e t) (e y) (by rw [← map_pow, hy3, map_one])
    (fun h => hy1 (e.injective (h.trans (map_one e).symm))) key

theorem fix_commutator_of_equiv_perm_four {M : Type*} [Group M]
    (e : M ≃* Equiv.Perm (Fin 4)) (α : MulAut M) (hα : ∀ x, α (α x) = x) {y : M}
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hαy : α y = y) :
    (∀ x ∈ commutator M, α x = x) ∧ Nat.card (commutator M) = 12 := by
  have hM₀map : (commutator M).map e.toMonoidHom = alternatingGroup (Fin 4) := by
    have h1 := map_commutator_eq (G := M) e.toMonoidHom
    have h2 : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
    rw [h2, ← _root_.commutator_def, commutator_perm_fin_four_eq_alternatingGroup] at h1
    exact h1
  have hchar : (commutator M).Characteristic := by
    rw [_root_.commutator_def]
    infer_instance
  have hcomap := Subgroup.characteristic_iff_comap_eq.mp hchar α
  have hαM₀ : ∀ x, x ∈ commutator M ↔ α x ∈ commutator M := by
    intro x
    constructor
    · intro hx
      rw [← hcomap] at hx
      exact hx
    · intro hx
      rw [← hcomap]
      exact hx
  let α₀ : MulAut (commutator M) := restrictMulAut α (commutator M) hαM₀
  let e₀ : commutator M ≃* alternatingGroup (Fin 4) :=
    (e.subgroupMap (commutator M)).trans (MulEquiv.subgroupCongr hM₀map)
  have he₀ : ∀ x : commutator M, ((e₀ x : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4)) =
      e x := fun x => rfl
  have hyM₀ : y ∈ commutator M := by
    have h1 : e y ∈ alternatingGroup (Fin 4) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      apply perm_four_sign_of_pow_three
      rw [← map_pow, hy3, map_one]
    rw [← hM₀map] at h1
    obtain ⟨x, hx, hxe⟩ := h1
    have : x = y := e.injective hxe
    exact this ▸ hx
  have hfix := mulAut_eq_of_alternating e₀
    GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
    (fun a => a ^ 3 = 1 ∧ a ≠ 1)
    (fun σ hσ a ha => perm_four_eq_one_of_commute_three σ hσ a ha.1 ha.2) α₀
    (fun x => Subtype.ext (by rw [restrictMulAut_apply, restrictMulAut_apply]; exact hα x))
    ⟨y, hyM₀⟩ (Subtype.ext (by rw [restrictMulAut_apply]; exact hαy))
    ⟨by
      apply Subtype.ext
      rw [Subgroup.coe_pow, he₀, ← map_pow, hy3, map_one, OneMemClass.coe_one],
    by
      intro h
      apply hy1
      have h' := congrArg Subtype.val h
      rw [he₀, OneMemClass.coe_one] at h'
      exact e.injective (h'.trans (map_one e).symm)⟩
  refine ⟨fun x hx => ?_, ?_⟩
  · have := hfix ⟨x, hx⟩
    rw [Subtype.ext_iff, restrictMulAut_apply] at this
    exact this
  · rw [Nat.card_congr e₀.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]

theorem fix_of_equiv_alternating_five {M : Type*} [Group M]
    (e : M ≃* alternatingGroup (Fin 5)) (α : MulAut M) (hα : ∀ x, α (α x) = x) {y : M}
    (hy5 : y ^ 5 = 1) (hy1 : y ≠ 1) (hαy : α y = y) : ∀ x, α x = x :=
  mulAut_eq_of_alternating e
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl (by norm_num))
    (fun a => a ^ 5 = 1 ∧ a ≠ 1)
    (fun σ hσ a ha => perm_five_eq_one_of_commute_five σ hσ a ha.1 ha.2) α hα y hαy
    ⟨by rw [← map_pow, hy5, map_one], fun h => hy1 (e.injective (h.trans (map_one e).symm))⟩

theorem not_index_two_of_equiv_alternating_five {M : Type*} [Group M]
    (e : M ≃* alternatingGroup (Fin 5)) (D : Subgroup M) (hD : D.index = 2) : False := by
  have hDn : D.Normal := Subgroup.normal_of_index_eq_two hD
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hDn' : (D.map e.toMonoidHom).Normal := hDn.map _ e.surjective
  have hidx : (D.map e.toMonoidHom).index = 2 := (Subgroup.index_map_equiv (H := D) e).trans hD
  rcases hDn'.eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.index_bot, nat_card_alternatingGroup] at hidx
    simp [Nat.factorial] at hidx
  · rw [h, Subgroup.index_top] at hidx
    omega

theorem pow_eq_one_of_inverted_of_sup {M : Type*} [Group M] {p : ℕ} (N C : Subgroup M)
    [N.Normal] (hN : ∀ x ∈ N, x ^ p = 1) (hC : IsCyclic C) (hsup : N ⊔ C = ⊤) {y t : M}
    (hinv : t * y * t⁻¹ = y⁻¹) : y ^ (2 * p) = 1 := by
  have hcomm : ∀ a b : M, a * b * a⁻¹ * b⁻¹ ∈ N := by
    intro a b
    have ha : a ∈ N ⊔ C := hsup ▸ Subgroup.mem_top a
    have hb : b ∈ N ⊔ C := hsup ▸ Subgroup.mem_top b
    obtain ⟨n₁, hn₁, c₁, hc₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
    obtain ⟨n₂, hn₂, c₂, hc₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    have hc : c₁ * c₂ = c₂ * c₁ :=
      congrArg Subtype.val (hC.commGroup.mul_comm ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩)
    rw [← QuotientGroup.eq_one_iff (N := N)]
    have e1 : ((n₁ : M) : M ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr hn₁
    have e2 : ((n₂ : M) : M ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr hn₂
    have e3 : ((c₁ : M) : M ⧸ N) * c₂ = c₂ * c₁ := by
      rw [← QuotientGroup.mk_mul, hc, QuotientGroup.mk_mul]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, e1, e2, one_mul]
    rw [e3]
    group
  have h1 : y * t * y⁻¹ * t⁻¹ = y ^ 2 := by
    have h2 : t * y⁻¹ * t⁻¹ = y := by
      calc t * y⁻¹ * t⁻¹ = (t * y * t⁻¹)⁻¹ := by group
        _ = y := by rw [hinv, inv_inv]
    calc y * t * y⁻¹ * t⁻¹ = y * (t * y⁻¹ * t⁻¹) := by group
      _ = y ^ 2 := by rw [h2, pow_two]
  have h2 := hN _ (h1 ▸ hcomm y t)
  rwa [← pow_mul] at h2

theorem not_dvd_psl2_subfield {p f k m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf0 : f ≠ 0)
    (hk0 : k ≠ 0) (hkf : k ∣ f) (hkf' : k ≠ f) (hm : p ^ f - 1 ≤ m) (hpm : ¬ p ∣ m)
    (hdvd : m ∣ p ^ k * (p ^ (2 * k) - 1) / 2) : False := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h2k : 2 * k ≤ f := by
    obtain ⟨c, rfl⟩ := hkf
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hf0
    have hc1 : c ≠ 1 := by
      rintro rfl
      simp at hkf'
    have := Nat.mul_le_mul_left k (show 2 ≤ c by omega)
    linarith
  have h9 : 9 ≤ p ^ (2 * k) := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ (2 * k) := Nat.pow_le_pow_right hp.pos (by omega)
  have hpow : p ^ (2 * k) ≤ p ^ f := Nat.pow_le_pow_right hp.pos h2k
  have hodd : Odd (p ^ (2 * k)) := (hp.odd_of_ne_two hp2).pow
  have hev : 2 ∣ p ^ (2 * k) - 1 := by
    obtain ⟨c, hc⟩ := hodd
    exact ⟨c, by omega⟩
  have hsplit : p ^ k * (p ^ (2 * k) - 1) / 2 = p ^ k * ((p ^ (2 * k) - 1) / 2) :=
    Nat.mul_div_assoc _ hev
  rw [hsplit] at hdvd
  have hcop : Nat.Coprime m (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)))
  have hdvd' := hcop.dvd_of_dvd_mul_left hdvd
  have hpos : 0 < (p ^ (2 * k) - 1) / 2 := by omega
  have := Nat.le_of_dvd hpos hdvd'
  omega

theorem not_dvd_pgl2_subfield {p f k m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf0 : f ≠ 0)
    (hk0 : k ≠ 0) (hkf : 2 * k ∣ f)
    (hm : (p ^ f % 4 = 1 ∧ m = p ^ f + 1) ∨ (p ^ f % 4 = 3 ∧ m = p ^ f - 1))
    (hpm : ¬ p ∣ m) (hdvd : m ∣ p ^ k * (p ^ (2 * k) - 1)) : False := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hcop : Nat.Coprime m (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)))
  have hdvd' := hcop.dvd_of_dvd_mul_left hdvd
  have h9 : 9 ≤ p ^ (2 * k) := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ (2 * k) := Nat.pow_le_pow_right hp.pos (by omega)
  have hle := Nat.le_of_dvd (by omega) hdvd'
  obtain ⟨c, rfl⟩ := hkf
  rcases c with _ | _ | c
  · simp at hf0
  ·
    have hsq : p ^ (2 * k * 1) = (p ^ k) ^ 2 := by ring
    rw [hsq] at hm
    have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
    obtain ⟨r, hr⟩ := hodd
    have hmod : (p ^ k) ^ 2 % 4 = 1 := by
      rw [hr]
      ring_nf
      omega
    rcases hm with ⟨-, hm⟩ | ⟨h3, -⟩
    · have : p ^ (2 * k) = (p ^ k) ^ 2 := by ring
      omega
    · omega
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hlt : p ^ (2 * k) * p ≤ p ^ (2 * k * (c + 1 + 1)) := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right hp.pos (by nlinarith)
    have : p ^ (2 * k) * 3 ≤ p ^ (2 * k * (c + 1 + 1)) :=
      le_trans (Nat.mul_le_mul_left _ hp3) hlt
    rcases hm with ⟨-, hm⟩ | ⟨-, hm⟩ <;> omega

theorem outer_involution_centralizer_maximal {K : Type u} [Field K] [Finite K] {p f : ℕ}
    [hp : Fact p.Prime] (hKcard : Nat.card K = p ^ f) (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {g : PGL2 K} (hg : g ^ 2 = 1) (hgJ : g ∉ pslRange K)
    (H : Subgroup (PGL2 K)) (hCH : Subgroup.centralizer ({g} : Set (PGL2 K)) ≤ H) :
    H = Subgroup.centralizer ({g} : Set (PGL2 K)) ∨ H = ⊤ := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)
  have hinj : Function.Injective toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  obtain ⟨U, w, hUc, hUcard, hgU, hwU, hww, hwinv, hC⟩ :=
    outer_involution_centralizer hK hcard hg hgJ
  have hCcard := card_outer_involution_centralizer hK hcard hg hgJ
  have hqodd : Odd (Nat.card K) := odd_card_of_isOddPrimePower hK
  set q := Nat.card K with hq
  set C := Subgroup.centralizer ({g} : Set (PGL2 K)) with hCdef
  set m := outerTorusOrder q with hmdef
  have hq5 : 5 ≤ q := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hm4 : m % 4 = 2 := outerTorusOrder_mod_four hqodd
  have hm6 : 6 ≤ m := six_le_outerTorusOrder hqodd hq5
  have hmq : (q % 4 = 1 ∧ m = q + 1) ∨ (q % 4 = 3 ∧ m = q - 1) := by
    obtain ⟨k, hk⟩ := hqodd
    rw [hmdef, outerTorusOrder]
    split_ifs with h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨by omega, rfl⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hKcard
    omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hKcard] at hqodd
    exact (Nat.not_even_iff_odd.mpr hqodd) ((Nat.even_pow' hf0).mpr even_two)
  have hpdvdq : p ∣ q := by
    rw [hKcard]
    exact dvd_pow_self p hf0
  clear_value m
  have hpm : ¬ p ∣ m := by
    intro hpm
    rcases hmq with ⟨-, hm⟩ | ⟨-, hm⟩
    · have h1 := Nat.dvd_sub hpm hpdvdq
      rw [hm, Nat.add_sub_cancel_left] at h1
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp h1)
    · have h1 : p ∣ q - m := Nat.dvd_sub hpdvdq hpm
      have h2 : q - m = 1 := by omega
      rw [h2] at h1
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp h1)
  have hJ2 := pslRange_index_eq_two hK
  have hJn : (pslRange K).Normal := pslRange_normal hK hcard
  have hgC : g ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hUC : U ≤ C := by rw [hC]; exact le_sup_left
  have hwC : w ∈ C := by rw [hC]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  set D := C.comap toPGL with hDdef
  set M := H.comap toPGL with hMdef
  have hDcard : Nat.card D = m := by
    have h1 : Nat.card C = 2 * Nat.card D := card_eq_two_mul_card_comap hK hcard hgC hgJ
    omega
  have hMcard : Nat.card H = 2 * Nat.card M := card_eq_two_mul_card_comap hK hcard (hCH hgC) hgJ
  have hDM : D ≤ M := Subgroup.comap_mono hCH
  have hmM : m ∣ Nat.card M := hDcard ▸ Subgroup.card_dvd_of_le hDM
  have hPSLcard : Nat.card (PSL2 K) = q * (q ^ 2 - 1) / 2 := psl2_card_formula K hK
  have hMPSL : Nat.card M ∣ q * (q ^ 2 - 1) / 2 := hPSLcard ▸ M.card_subgroup_dvd_card
  have hPGLcard : Nat.card (PGL2 K) = q * (q ^ 2 - 1) := pgl2_card_formula K
  have hMeqD : Nat.card M ≤ m → H = C ∨ H = ⊤ := by
    intro hle
    have hMD : M = D := (Subgroup.eq_of_le_of_card_ge hDM (by omega)).symm
    left
    refine (Subgroup.eq_of_le_of_card_ge hCH ?_).symm
    rw [hCcard, hMcard, hMD, hDcard]
  have hMtop : Nat.card M = Nat.card (PSL2 K) → H = C ∨ H = ⊤ := by
    intro hMeq
    right
    apply Subgroup.eq_top_of_card_eq
    rw [hMcard, hMeq, hPSLcard, hPGLcard]
    have hev : Even (q * (q ^ 2 - 1)) := by
      apply Nat.even_mul.mpr
      right
      exact Nat.Odd.sub_odd hqodd.pow odd_one
    obtain ⟨r, hr⟩ := hev
    omega
  obtain ⟨x₀, hx₀⟩ := hUc.exists_generator
  have hx₀ord : orderOf (x₀ : PGL2 K) = m := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hx₀, hUcard]
  have hsqJ : ∀ x : PGL2 K, x * x ∈ pslRange K :=
    fun x => Subgroup.mul_self_mem_of_index_two hJ2 x
  have hx₀J : (x₀ : PGL2 K) ∉ pslRange K := by
    intro hx
    apply hgJ
    obtain ⟨k, hk⟩ := hx₀ ⟨g, hgU⟩
    have h' : (x₀ : PGL2 K) ^ k = g := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [← h']
    exact Subgroup.zpow_mem _ hx k
  obtain ⟨t, htC, htJ, htinv, htt⟩ : ∃ t : PGL2 K, t ∈ C ∧ t ∈ pslRange K ∧
      (∀ x ∈ U, t * x * t⁻¹ = x⁻¹) ∧ t * t = 1 := by
    by_cases hwJ : w ∈ pslRange K
    · exact ⟨w, hwC, hwJ, hwinv, hww⟩
    · refine ⟨x₀ * w, C.mul_mem (hUC x₀.2) hwC, ?_, ?_, ?_⟩
      · exact (Subgroup.mul_mem_iff_of_index_two hJ2).mpr (iff_of_false hx₀J hwJ)
      · intro x hx
        have hcomm : (x₀ : PGL2 K) * x⁻¹ * (x₀ : PGL2 K)⁻¹ = x⁻¹ := by
          have := hUc.commGroup.mul_comm x₀ ⟨x⁻¹, U.inv_mem hx⟩
          have h' : (x₀ : PGL2 K) * x⁻¹ = x⁻¹ * x₀ := congrArg Subtype.val this
          rw [h']
          group
        calc (x₀ : PGL2 K) * w * x * ((x₀ : PGL2 K) * w)⁻¹ =
            x₀ * (w * x * w⁻¹) * (x₀ : PGL2 K)⁻¹ := by group
          _ = x⁻¹ := by rw [hwinv x hx, hcomm]
      · have h1 := hwinv x₀ x₀.2
        calc (x₀ : PGL2 K) * w * (x₀ * w) = x₀ * (w * x₀ * w⁻¹) * (w * w) := by group
          _ = 1 := by rw [h1, hww]; group
  set y : PGL2 K := (x₀ : PGL2 K) * x₀ with hydef
  have hyJ : y ∈ pslRange K := hsqJ _
  have hyU : y ∈ U := U.mul_mem x₀.2 x₀.2
  have hyord : orderOf y = m / 2 := by
    rw [hydef, ← pow_two, orderOf_pow' _ two_ne_zero, hx₀ord]
    have : Nat.gcd m 2 = 2 := Nat.gcd_eq_right (by omega)
    rw [this]
  obtain ⟨yh, hyh⟩ := hyJ
  obtain ⟨th, hth⟩ := htJ
  have hyhord : orderOf yh = m / 2 := by rw [← orderOf_injective toPGL hinj, hyh, hyord]
  have hyhD : yh ∈ D := by
    change toPGL yh ∈ C
    rw [hyh]
    exact hUC hyU
  have hthD : th ∈ D := by
    change toPGL th ∈ C
    rw [hth]
    exact htC
  have hinv : th * yh * th⁻¹ = yh⁻¹ := by
    apply hinj
    rw [map_mul, map_mul, map_inv, map_inv, hyh, hth]
    exact htinv y hyU
  have hyh2 : yh ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hyhord] at this
    have := Nat.le_of_dvd two_pos this
    omega
  have hnc : yh * th ≠ th * yh := by
    intro h
    apply hyh2
    have : yh = yh⁻¹ := by
      rw [← hinv, ← h]
      group
    rw [pow_two]
    nth_rewrite 2 [this]
    group
  have hyhM : yh ∈ M := hDM hyhD
  have hthM : th ∈ M := hDM hthD
  set yM : M := ⟨yh, hyhM⟩ with hyMdef
  set tM : M := ⟨th, hthM⟩ with htMdef
  have hinvM : tM * yM * tM⁻¹ = yM⁻¹ := Subtype.ext hinv
  have hncM : yM * tM ≠ tM * yM := fun h => hnc (congrArg Subtype.val h)
  have hyMord : orderOf yM = m / 2 := by rw [Subgroup.orderOf_mk, hyhord]
  have hyM1 : yM ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyMord
    omega
  let φ : MulAut (PSL2 K) := pgl2InnerAutPSL2 K hK hcard g
  have hφ : ∀ x, toPGL (φ x) = g * toPGL x * g⁻¹ := fun x =>
    toPGL_pgl2InnerAutPSL2_apply K hK hcard g x
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hg)
  have hφφ : ∀ x, φ (φ x) = x := by
    intro x
    apply hinj
    rw [hφ, hφ, hg']
    calc g * (g * toPGL x * g) * g = (g * g) * toPGL x * (g * g) := by group
      _ = toPGL x := by rw [← pow_two, hg]; group
  have hφM : ∀ x, x ∈ M ↔ φ x ∈ M := by
    intro x
    change toPGL x ∈ H ↔ toPGL (φ x) ∈ H
    rw [hφ]
    constructor
    · intro hx
      exact H.mul_mem (H.mul_mem (hCH hgC) hx) (H.inv_mem (hCH hgC))
    · intro hx
      have := H.mul_mem (H.mul_mem (H.inv_mem (hCH hgC)) hx) (hCH hgC)
      simpa [mul_assoc] using this
  have hφyh : φ yh = yh := by
    apply hinj
    rw [hφ, hyh]
    have : y * g = g * y := by
      have := hUc.commGroup.mul_comm ⟨y, hyU⟩ ⟨g, hgU⟩
      exact congrArg Subtype.val this
    rw [← this]
    group
  let α : MulAut M := restrictMulAut φ M hφM
  have hαα : ∀ x, α (α x) = x := fun x => Subtype.ext (by
    rw [restrictMulAut_apply, restrictMulAut_apply]
    exact hφφ x)
  have hαy : α yM = yM := Subtype.ext (by rw [restrictMulAut_apply]; exact hφyh)
  have hfixN : ∀ N : Subgroup M, (∀ x ∈ N, α x = x) → 2 * m ≤ Nat.card N → False := by
    intro N hN hcardN
    have hNC : (N.map M.subtype).map toPGL ≤ C := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hφ x
      have h2 : φ x = x := by
        have := hN x hx
        rw [Subtype.ext_iff, restrictMulAut_apply] at this
        exact this
      rw [h2] at h1
      calc toPGL x * g = g * toPGL x * g⁻¹ * g := by rw [← h1]
        _ = g * toPGL x := by group
    have hNcard : Nat.card ((N.map M.subtype).map toPGL) = Nat.card N := by
      rw [← Nat.card_congr ((N.map M.subtype).equivMapOfInjective toPGL hinj).toEquiv,
        ← Nat.card_congr (N.equivMapOfInjective M.subtype M.subtype_injective).toEquiv]
    have hNeq : (N.map M.subtype).map toPGL = C :=
      Subgroup.eq_of_le_of_card_ge hNC (by rw [hNcard, hCcard]; exact hcardN)
    have hgN : g ∈ (N.map M.subtype).map toPGL := hNeq ▸ hgC
    obtain ⟨x, -, hx⟩ := hgN
    exact hgJ ⟨x, hx⟩
  have hgcd : Nat.gcd (q - 1) 2 = 2 := by
    apply Nat.gcd_eq_right
    obtain ⟨k, hk⟩ := hqodd
    exact ⟨k, by omega⟩
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hKcard M with
    hEA | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hzcard, -⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨h16, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m', r, -, -, N, Cc, hNn, hNea, -, hCc, -, -, hsup⟩ | ⟨k, hk0, hkf, ⟨eL⟩⟩ |
      ⟨k, hk0, hkf, ⟨eG⟩⟩
  ·
    exact absurd (hEA.toIsMulCommutative.is_comm.comm yM tM) hncM
  ·
    exact absurd (hcyc.commGroup.mul_comm yM tM) hncM
  ·
    rw [← hq, hgcd] at hz
    have hmz : m ∣ 2 * z := hzcard ▸ hmM
    have h2 : 2 ∣ q + 1 := by obtain ⟨k, hk⟩ := hqodd; exact ⟨k + 1, by omega⟩
    have h2' : 2 ∣ q - 1 := by obtain ⟨k, hk⟩ := hqodd; exact ⟨k, by omega⟩
    rcases hz with hz | hz
    · have h1 : 2 * z ∣ q - 1 := by
        rw [← Nat.div_mul_cancel h2', mul_comm]
        exact Nat.mul_dvd_mul_right hz 2
      rcases hmq with ⟨-, hm⟩ | ⟨-, hm⟩
      · exfalso
        have := Nat.le_of_dvd (by omega) (hmz.trans h1)
        omega
      · exact hMeqD (by rw [hzcard]; exact Nat.le_of_dvd (by omega) (hm ▸ h1))
    · have h1 : 2 * z ∣ q + 1 := by
        rw [← Nat.div_mul_cancel h2, mul_comm]
        exact Nat.mul_dvd_mul_right hz 2
      rcases hmq with ⟨-, hm⟩ | ⟨-, hm⟩
      · exact hMeqD (by rw [hzcard]; exact Nat.le_of_dvd (by omega) (hm ▸ h1))
      · exfalso
        have h3 : m ∣ q + 1 - m := Nat.dvd_sub (hmz.trans h1) dvd_rfl
        have h4 : q + 1 - m = 2 := by omega
        rw [h4] at h3
        have := Nat.le_of_dvd two_pos h3
        omega
  ·
    exfalso
    have hM12 : Nat.card M = 12 := by
      rw [Nat.card_congr eA4.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    have hm12 : m = 6 := by
      have hdvd : m ∣ 12 := hM12 ▸ hmM
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases m <;> omega
    have hy3 : yM ^ 3 = 1 := by
      have : orderOf yM = 3 := by rw [hyMord, hm12]
      rw [← this]
      exact pow_orderOf_eq_one yM
    exact not_inverted_of_equiv_alternating_four eA4 hy3 hyM1 hinvM
  ·
    exfalso
    have hM24 : Nat.card M = 24 := by
      rw [Nat.card_congr eS4.toEquiv, Nat.card_perm]
      simp [Nat.factorial]
    have hm6' : m = 6 := by
      have hdvd : m ∣ 24 := hM24 ▸ hmM
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases m <;> omega
    have hy3 : yM ^ 3 = 1 := by
      have : orderOf yM = 3 := by rw [hyMord, hm6']
      rw [← this]
      exact pow_orderOf_eq_one yM
    obtain ⟨hfix, h12⟩ := fix_commutator_of_equiv_perm_four eS4 α hαα hy3 hyM1 hαy
    exact hfixN (commutator M) hfix (by rw [h12, hm6'])
  ·
    have hM60 : Nat.card M = 60 := by
      rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    have hm' : m = 6 ∨ m = 10 ∨ m = 30 := by
      have hdvd : m ∣ 60 := hM60 ▸ hmM
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases m <;> omega
    rcases hm' with hm' | hm' | hm'
    ·
      rcases hmq with ⟨hq4, hm⟩ | ⟨hq4, hm⟩
      · have hq5' : q = 5 := by omega
        apply hMtop
        rw [hM60, hPSLcard, hq5']
        norm_num
      · exfalso
        have hq7 : q = 7 := by omega
        rw [hM60, hq7] at hMPSL
        norm_num at hMPSL
    ·
      exfalso
      have hy5 : yM ^ 5 = 1 := by
        have : orderOf yM = 5 := by rw [hyMord, hm']
        rw [← this]
        exact pow_orderOf_eq_one yM
      have hfix := fix_of_equiv_alternating_five eA5 α hαα hy5 hyM1 hαy
      exact hfixN ⊤ (fun x _ => hfix x) (by rw [Subgroup.card_top, hM60, hm']; norm_num)
    ·
      exfalso
      apply not_index_two_of_equiv_alternating_five eA5 (D.subgroupOf M)
      have h1 := (D.subgroupOf M).card_mul_index
      have h2 : Nat.card (D.subgroupOf M) = 30 := by
        rw [← hm', ← hDcard]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv
      rw [h2, hM60] at h1
      omega
  ·
    exfalso
    have hN : ∀ x ∈ N, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
    have h1 := pow_eq_one_of_inverted_of_sup N Cc hN hCc hsup hinvM
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hyMord] at h2
    have hodd : Odd (m / 2) := by
      refine Nat.odd_iff.mpr ?_
      omega
    have h3 : m / 2 ∣ p :=
      (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr hodd))
        h2)
    rcases (Nat.dvd_prime hp.out).mp h3 with h4 | h4
    · omega
    · apply hpm
      exact ⟨2, by omega⟩
  ·
    have hGF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
    have hGFodd : IsOddPrimePower (Nat.card (GaloisField p k)) :=
      ⟨p, k, hp.out, hp.out.odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.mpr hk0, hGF⟩
    have hMc : Nat.card M = p ^ k * ((p ^ k) ^ 2 - 1) / 2 := by
      rw [Nat.card_congr eL.toEquiv]
      have := psl2_card_formula (GaloisField p k) hGFodd
      rw [hGF] at this
      exact this
    have hpk : (p ^ k) ^ 2 = p ^ (2 * k) := by rw [← pow_mul, mul_comm]
    by_cases hkf' : k = f
    · subst hkf'
      apply hMtop
      rw [hMc, hPSLcard, hKcard]
    · exfalso
      refine not_dvd_psl2_subfield hp.out hp2 hf0 hk0 hkf hkf' ?_ hpm ?_
      · rw [← hKcard]
        rcases hmq with ⟨-, hm⟩ | ⟨-, hm⟩ <;> omega
      · rw [← hpk, ← hMc]
        exact hmM
  ·
    exfalso
    have hGF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
    have hMc : Nat.card M = p ^ k * ((p ^ k) ^ 2 - 1) := by
      rw [Nat.card_congr eG.toEquiv]
      have := pgl2_card_formula (GaloisField p k)
      rw [hGF] at this
      exact this
    have hpk : (p ^ k) ^ 2 = p ^ (2 * k) := by rw [← pow_mul, mul_comm]
    refine not_dvd_pgl2_subfield hp.out hp2 hf0 hk0 hkf (m := m) ?_ hpm ?_
    · rw [← hKcard]
      exact hmq
    · rw [← hpk, ← hMc]
      exact hmM

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
