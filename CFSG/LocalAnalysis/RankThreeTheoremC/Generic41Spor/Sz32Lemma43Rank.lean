module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup
open scoped commutatorElement

section Abstract

variable {X : Type*} [Group X]

theorem szj_pow_comm_aux {f g t : X} (htg : Commute t g)
    (h : g * f = t * (f * g)) (n : ℕ) : g ^ n * f = t ^ n * (f * g ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc g ^ (n + 1) * f = g * (g ^ n * f) := by rw [pow_succ', mul_assoc]
      _ = g * (t ^ n * (f * g ^ n)) := by rw [ih]
      _ = (g * t ^ n) * (f * g ^ n) := by rw [mul_assoc]
      _ = (t ^ n * g) * (f * g ^ n) := by rw [(htg.symm.pow_right n).eq]
      _ = t ^ n * ((g * f) * g ^ n) := by simp only [mul_assoc]
      _ = t ^ n * ((t * (f * g)) * g ^ n) := by rw [h]
      _ = t ^ (n + 1) * (f * g ^ (n + 1)) := by
          rw [pow_succ t n, pow_succ' g n]
          simp only [mul_assoc]

theorem szj_mul_pow_aux {f g t : X} (htf : Commute t f) (htg : Commute t g)
    (h : g * f = t * (f * g)) (n : ℕ) : (f * g) ^ n = t ^ (n.choose 2) * (f ^ n * g ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 := szj_pow_comm_aux htg h n
    have hfn : f ^ n * t ^ n = t ^ n * f ^ n := ((htf.pow_pow n n).eq).symm
    have hc : (n + 1).choose 2 = n.choose 2 + n := by
      rw [show (2:ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    calc (f * g) ^ (n + 1) = (f * g) ^ n * (f * g) := pow_succ _ _
      _ = (t ^ n.choose 2 * (f ^ n * g ^ n)) * (f * g) := by rw [ih]
      _ = t ^ n.choose 2 * (f ^ n * (g ^ n * f) * g) := by simp only [mul_assoc]
      _ = t ^ n.choose 2 * (f ^ n * (t ^ n * (f * g ^ n)) * g) := by rw [h2]
      _ = t ^ n.choose 2 * (t ^ n * (f ^ n * (f * g ^ n)) * g) := by
          rw [← mul_assoc (f ^ n) (t ^ n), hfn, mul_assoc (t ^ n)]
      _ = t ^ (n + 1).choose 2 * (f ^ (n + 1) * g ^ (n + 1)) := by
          rw [hc, pow_add, pow_succ f n, pow_succ g n]
          simp only [mul_assoc]

section Facts

variable {Q : Subgroup X} {a c y x : X}

theorem szj_Z_le_Q (hQ : Sz32QFacts Q a c y x) : sz32Z a c ≤ Q :=
  (le_sup_left : sz32Z a c ≤ sz32Om a c y).trans hQ.Om_le

theorem szj_pow5_mul (hQ : Sz32QFacts Q a c y x) {f g : X} (hf : f ∈ Q) (hg : g ∈ Q) :
    (f * g) ^ 5 = f ^ 5 * g ^ 5 := by
  have htmem : ⁅g, f⁆ ∈ sz32Z a c := hQ.comm_eq ▸ Subgroup.commutator_mem_commutator hg hf
  have htQ : ⁅g, f⁆ ∈ Q := szj_Z_le_Q hQ htmem
  have hcen : ∀ q ∈ Q, q * ⁅g, f⁆ = ⁅g, f⁆ * q := fun q hq => (hQ.center _ htQ).2 htmem q hq
  have htf : Commute ⁅g, f⁆ f := (hcen f hf).symm
  have htg : Commute ⁅g, f⁆ g := (hcen g hg).symm
  have h : g * f = ⁅g, f⁆ * (f * g) := by simp [commutatorElement_def, mul_assoc]
  have ht5 : ⁅g, f⁆ ^ 5 = 1 := hQ.Z_elem.2 _ htmem
  rw [szj_mul_pow_aux htf htg h 5, show Nat.choose 5 2 = 5 * 2 from by decide, pow_mul, ht5]
  simp

theorem szj_exists_card_pow [Finite X] {E : Subgroup X} (hE : IsElemAbelian 5 E) :
    ∃ k : ℕ, Nat.card E = 5 ^ k := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hpg : IsPGroup 5 E := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 (g : X) g.2⟩
  exact hpg.exists_card_eq

theorem szj_card_le [Finite X] (hQ : Sz32QFacts Q a c y x)
    {U F : Subgroup X} (hUe : IsElemAbelian 5 U) (hUcard : Nat.card U = 5 ^ 2)
    (hUZ : Nat.card (U ⊓ sz32Z a c : Subgroup X) ≤ 5)
    (hUF : U ≤ F) (hFQ : F ≤ Q) (hΩ : ∀ f ∈ F, f ^ 5 = 1 → f ∈ U) :
    Nat.card F ≤ 5 ^ 3 := by
  let ψ : F →* X := MonoidHom.mk' (fun f : F => (f : X) ^ 5)
    (fun f g => szj_pow5_mul hQ (hFQ f.2) (hFQ g.2))
  have hker : ψ.ker = U.subgroupOf F := by
    ext f
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact hΩ f f.2 h
    · intro h
      exact hUe.2 f h
  have hrange : ψ.range ≤ U ⊓ sz32Z a c := by
    rintro _ ⟨f, rfl⟩
    have h1 : (f : X) ^ 5 ∈ F := F.pow_mem f.2 5
    have h2 : (f : X) ^ 5 ∈ sz32Z a c := hQ.pow5 f (hFQ f.2)
    have h3 : ((f : X) ^ 5) ^ 5 = 1 := by
      rw [← pow_mul]
      exact hQ.exp f (hFQ f.2)
    exact ⟨hΩ _ h1 h3, h2⟩
  have hcardker : Nat.card ψ.ker = 5 ^ 2 := by
    rw [hker, ← hUcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUF).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range ψ
  have hrcard : Nat.card ψ.range ≤ 5 := (Subgroup.card_le_of_le hrange).trans hUZ
  rw [hcardker] at hmul
  calc Nat.card F = 5 ^ 2 * Nat.card ψ.range := hmul.symm
    _ ≤ 5 ^ 2 * 5 := Nat.mul_le_mul_left _ hrcard
    _ = 5 ^ 3 := by norm_num

theorem szj_omega [Finite X] (hQ : Sz32QFacts Q a c y x)
    {U F : Subgroup X} (hUe : IsElemAbelian 5 U) (hUcard : Nat.card U = 5 ^ 2)
    (hUF : U ≤ F) (hFQ : F ≤ Q) (hrank : CFSG.Open.pRank 5 F ≤ 2) :
    ∀ f ∈ F, f ^ 5 = 1 → f ∈ U := by
  intro f hf hf5
  haveI hOmc : IsMulCommutative (sz32Om a c y) := hQ.Om_elem.1
  have hfOm : f ∈ sz32Om a c y := hQ.Om_all f (hFQ hf) hf5
  have hUOm : U ≤ sz32Om a c y := fun u hu => hQ.Om_all u (hFQ (hUF hu)) (hUe.2 u hu)
  have hEOm : U ⊔ Subgroup.zpowers f ≤ sz32Om a c y :=
    sup_le hUOm (Subgroup.zpowers_le.2 hfOm)
  have hEF : U ⊔ Subgroup.zpowers f ≤ F := sup_le hUF (Subgroup.zpowers_le.2 hf)
  have hEel : IsElemAbelian 5 (U ⊔ Subgroup.zpowers f : Subgroup X) :=
    ⟨isMulCommutative_anti hEOm, fun e he => hQ.Om_elem.2 e (hEOm he)⟩
  obtain ⟨k, hk⟩ := szj_exists_card_pow hEel
  have hk2 : k ≤ 2 := (CFSG.SectionRank.le_pRank (by norm_num) hEF hEel hk).trans hrank
  have hcard : Nat.card (U ⊔ Subgroup.zpowers f : Subgroup X) ≤ 5 ^ 2 := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk2
  have hUE : U = U ⊔ Subgroup.zpowers f :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hUcard]; exact hcard)
  have hfE : f ∈ U ⊔ Subgroup.zpowers f := Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  rwa [← hUE] at hfE

end Facts

theorem szj_card_mul_le [Finite X] {P A B : Subgroup X}
    (hAB : ∀ s ∈ P, ∃ a ∈ A, ∃ b ∈ B, s = a * b) :
    Nat.card P * Nat.card (A ⊓ B : Subgroup X) ≤ Nat.card A * Nat.card B := by
  choose! f hfA g hgB hfg using hAB
  let F : P × (A ⊓ B : Subgroup X) → A × B := fun q =>
    (⟨f q.1 * q.2, A.mul_mem (hfA q.1 q.1.2) (Subgroup.mem_inf.1 q.2.2).1⟩,
      ⟨(q.2 : X)⁻¹ * g q.1,
        B.mul_mem (B.inv_mem (Subgroup.mem_inf.1 q.2.2).2) (hgB q.1 q.1.2)⟩)
  have hF : Function.Injective F := by
    rintro ⟨p, t⟩ ⟨p', t'⟩ h
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hpp : (p : X) = p' := by
      calc (p : X) = f p * g p := hfg p p.2
        _ = (f p * t) * ((t : X)⁻¹ * g p) := by group
        _ = (f p' * t') * ((t' : X)⁻¹ * g p') := by rw [h1, h2]
        _ = f p' * g p' := by group
        _ = p' := (hfg p' p'.2).symm
    have hpp' : p = p' := Subtype.ext hpp
    subst hpp'
    have : (t : X) = t' := mul_left_cancel h1
    exact Prod.ext rfl (Subtype.ext this)
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_prod] at this

theorem szj_rank_step [Finite X] {Q : Subgroup X} {a c y x : X} (hQ : Sz32QFacts Q a c y x)
    {U A B : Subgroup X} (hUe : IsElemAbelian 5 U) (hUcard : Nat.card U = 5 ^ 2)
    (hUZ : Nat.card (U ⊓ sz32Z a c : Subgroup X) ≤ 5)
    (hAQ : A ≤ Q) (hBQ : B ≤ Q) (hUA : U ≤ A) (hUB : U ≤ B)
    (hAB : ∀ s ∈ Q, ∃ a ∈ A, ∃ b ∈ B, s = a * b) :
    3 ≤ CFSG.Open.pRank 5 A ∨ 3 ≤ CFSG.Open.pRank 5 B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA3, hB3⟩ := hcon
  have hA := szj_card_le hQ hUe hUcard hUZ hUA hAQ
    (szj_omega hQ hUe hUcard hUA hAQ (by omega))
  have hB := szj_card_le hQ hUe hUcard hUZ hUB hBQ
    (szj_omega hQ hUe hUcard hUB hBQ (by omega))
  have hprod := szj_card_mul_le hAB
  have hUAB : U ≤ A ⊓ B := le_inf hUA hUB
  have h25 : 5 ^ 2 ≤ Nat.card (A ⊓ B : Subgroup X) := by
    rw [← hUcard]
    exact Subgroup.card_le_of_le hUAB
  rw [hQ.card] at hprod
  have h1 : Nat.card A * Nat.card B ≤ 5 ^ 3 * 5 ^ 3 := Nat.mul_le_mul hA hB
  have h2 : 5 ^ 5 * 5 ^ 2 ≤ 5 ^ 5 * Nat.card (A ⊓ B : Subgroup X) := Nat.mul_le_mul_left _ h25
  omega

end Abstract

section GLevel

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}
  {a c y : G}

theorem szj_Z_eq (hP : Sz32Struct P x J a c y) :
    Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x = sz32Z a c := by
  rw [hP.facts.x_eq]
  rfl

theorem szj_mem_map_conj_iff {V : Subgroup G} {l s : G} :
    s ∈ V.map (MulAut.conj l).toMonoidHom ↔ l⁻¹ * s * l ∈ V := by
  simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem szj_rank_conj (hP : Sz32Struct P x J a c y) (hZ : Sz32ZFacts P M x (a ^ 5))
    {U : Subgroup G} (hU : Sz32Plane P x a c y U) (l : G) {A B : Subgroup G}
    (hUS : U ≤ (P : Subgroup G).map (MulAut.conj l).toMonoidHom)
    (hAS : A ≤ (P : Subgroup G).map (MulAut.conj l).toMonoidHom)
    (hBS : B ≤ (P : Subgroup G).map (MulAut.conj l).toMonoidHom)
    (hUA : U ≤ A) (hUB : U ≤ B)
    (hAB : ∀ s ∈ (P : Subgroup G).map (MulAut.conj l).toMonoidHom, ∃ a ∈ A, ∃ b ∈ B, s = a * b) :
    3 ≤ CFSG.Open.pRank 5 A ∨ 3 ≤ CFSG.Open.pRank 5 B := by
  have hmem : ∀ (V : Subgroup G) (s : G),
      s ∈ V.map (MulAut.conj l⁻¹).toMonoidHom ↔ l * s * l⁻¹ ∈ V := by
    intro V s
    rw [szj_mem_map_conj_iff, inv_inv]
  have hmemS : ∀ s : G, s ∈ (P : Subgroup G).map (MulAut.conj l).toMonoidHom ↔
      l⁻¹ * s * l ∈ (P : Subgroup G) := fun s => szj_mem_map_conj_iff
  have hle : ∀ D : Subgroup G, D ≤ (P : Subgroup G).map (MulAut.conj l).toMonoidHom →
      D.map (MulAut.conj l⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    intro D hD g hg
    rw [hmem] at hg
    have := (hmemS _).1 (hD hg)
    simpa [mul_assoc] using this
  have hback : ∀ D : Subgroup G,
      (D.map (MulAut.conj l⁻¹).toMonoidHom).map (MulAut.conj l).toMonoidHom = D := by
    intro D
    ext g
    rw [szj_mem_map_conj_iff, hmem]
    simp [mul_assoc]
  have hrank : ∀ D : Subgroup G,
      CFSG.Open.pRank 5 (D.map (MulAut.conj l⁻¹).toMonoidHom) ≤ CFSG.Open.pRank 5 D := by
    intro D
    have h1 := CFSG.SectionRank.pRank_le_map (p := 5) (by norm_num) (MulAut.conj l).toMonoidHom
      (MulAut.conj l).injective (D.map (MulAut.conj l⁻¹).toMonoidHom)
    rwa [hback D] at h1
  have hUe : IsElemAbelian 5 (U.map (MulAut.conj l⁻¹).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hU.abs.elem _
  have hUcard : Nat.card (U.map (MulAut.conj l⁻¹).toMonoidHom) = 5 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj l⁻¹).injective, hU.abs.card]
  have hUZ : Nat.card ((U.map (MulAut.conj l⁻¹).toMonoidHom) ⊓ sz32Z a c : Subgroup G) ≤ 5 := by
    by_contra hgt
    push Not at hgt
    have hdvd : Nat.card ((U.map (MulAut.conj l⁻¹).toMonoidHom) ⊓ sz32Z a c : Subgroup G) ∣
        5 ^ 2 := by
      rw [← hUcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h25 : Nat.card ((U.map (MulAut.conj l⁻¹).toMonoidHom) ⊓ sz32Z a c : Subgroup G) =
        5 ^ 2 := by
      obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow (by norm_num)).1 hdvd
      interval_cases i <;> simp_all
    have hU1Z : (U.map (MulAut.conj l⁻¹).toMonoidHom) ⊓ sz32Z a c =
        U.map (MulAut.conj l⁻¹).toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h25, hUcard])
    have hU1eq : U.map (MulAut.conj l⁻¹).toMonoidHom = sz32Z a c :=
      Subgroup.eq_of_le_of_card_ge (hU1Z ▸ inf_le_right) (by rw [hUcard, hP.facts.Z_card])
    have hUeq : (sz32Z a c).map (MulAut.conj l).toMonoidHom = U := by
      rw [← hU1eq, hback]
    have hwc := hZ.Z_wc l
    rw [szj_Z_eq hP] at hwc
    have hZP : (sz32Z a c).map (MulAut.conj l).toMonoidHom ≤ (P : Subgroup G) :=
      hUeq ▸ hU.le_P
    have hUZ' : U = sz32Z a c := by rw [← hUeq]; exact hwc hZP
    have hinf := hU.abs.inf_Z
    rw [hUZ', inf_idem] at hinf
    have h1 : Nat.card (sz32Z a c) = 5 ^ 2 := hP.facts.Z_card
    have h2 : Nat.card (Subgroup.zpowers x) = 5 := by
      rw [Nat.card_zpowers]
      exact hP.pres_P.x_ord
    rw [hinf, h2] at h1
    omega
  have hprod : ∀ s ∈ (P : Subgroup G), ∃ a ∈ A.map (MulAut.conj l⁻¹).toMonoidHom,
      ∃ b ∈ B.map (MulAut.conj l⁻¹).toMonoidHom, s = a * b := by
    intro s hs
    have hsS : l * s * l⁻¹ ∈ (P : Subgroup G).map (MulAut.conj l).toMonoidHom :=
      (hmemS _).2 (by simpa [mul_assoc] using hs)
    obtain ⟨a', ha', b', hb', hab'⟩ := hAB _ hsS
    refine ⟨l⁻¹ * a' * l, ?_, l⁻¹ * b' * l, ?_, ?_⟩
    · rw [hmem]
      simpa [mul_assoc] using ha'
    · rw [hmem]
      simpa [mul_assoc] using hb'
    · calc s = l⁻¹ * (l * s * l⁻¹) * l := by group
        _ = l⁻¹ * (a' * b') * l := by rw [hab']
        _ = (l⁻¹ * a' * l) * (l⁻¹ * b' * l) := by group
  have key := szj_rank_step hP.facts hUe hUcard hUZ (hle A hAS) (hle B hBS)
    (Subgroup.map_mono hUA) (Subgroup.map_mono hUB) hprod
  exact key.imp (fun h => h.trans (hrank A)) (fun h => h.trans (hrank B))

end GLevel

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
