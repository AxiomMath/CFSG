module

public import CFSG.GH74.Uniqueness.Section7Lemma711Quot
public import CFSG.GH74.Uniqueness.Section7Lemma711Bender
public import CFSG.GH74.Uniqueness.Section7Theta
public import CFSG.GH74.Uniqueness.Section7Stage2Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem mem_normalizer_sup_of_mem_normalizer {A B : Subgroup X} {g : X}
    (hA : g ∈ normalizer (A : Set X)) (hB : g ∈ normalizer (B : Set X)) :
    g ∈ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  rw [← conjugate_eq_iff_mem_normalizer] at hA hB ⊢
  have hc : ∀ C : Subgroup X, conjugate C g = C.map (MulAut.conj g⁻¹).toMonoidHom :=
    fun C => rfl
  rw [hc, Subgroup.map_sup, ← hc, ← hc, hA, hB]

omit [Finite X] in
theorem mem_normalizer_inf_of_mem_normalizer {A B : Subgroup X} {g : X}
    (hA : g ∈ normalizer (A : Set X)) (hB : g ∈ normalizer (B : Set X)) :
    g ∈ normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [← conjugate_eq_iff_mem_normalizer] at hA hB ⊢
  rw [conjugate_inf, hA, hB]

omit [Finite X] in
theorem le_of_isSylowOf_of_isPGroup_normal {p : ℕ} [Fact p.Prime] {Q R K : Subgroup X}
    (hR : ABGLocalTools.IsSylowOf p R K) (hQK : Q ≤ K) (hKQ : K ≤ normalizer (Q : Set X))
    (hQp : IsPGroup p Q) : Q ≤ R := by
  obtain ⟨RN, rfl⟩ := hR
  have hn : (Q.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mpr hKQ
  have : (Q.subgroupOf K).Normal := hn
  have hle : Q.subgroupOf K ≤ (RN : Subgroup ↥K) :=
    IsPGroup.le_sylow_of_normal (N := Q.subgroupOf K) (hQp.comap_subtype (K := K)) RN
  intro x hx
  exact ⟨⟨x, hQK hx⟩, hle (show (⟨x, hQK hx⟩ : ↥K) ∈ Q.subgroupOf K from hx), rfl⟩

theorem ZDSetup.lemma711
    (S : ZDSetup X Z M) : Lemma711Stmt Z M := by
  intro z p W β Q t R P₁ hd h2rank h7E m hm
  classical
  have hZ := S.invariant
  have h := S.prodDisc
  have hcand := hd.tmax.cand
  have hp : p.Prime := hcand.prime
  have hp2 : p ≠ 2 := hcand.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hzZ : z ∈ Z := hcand.mem_Z
  have hzM : z ∈ M := hcand.mem_M
  have hzN : z ∈ normalizer (Q : Set X) := hd.adm.z_norm
  have htN : t ∈ normalizer (Q : Set X) := hd.t_norm_Q
  have htM : t ∉ M := by
    intro htM
    apply hd.beta_ne
    rw [← hd.t_swap]
    exact (h.conjugate_eq_iff_mem (self_mem_omega M)).mpr htM
  have hQM : Q ≤ M := hd.adm.le_E.trans (inf_le_left.trans inf_le_left)
  have hNtop : normalizer (Q : Set X) ≠ ⊤ := by
    intro htop
    have hnormal : Q.Normal := ⟨fun n hn g => by
      have hg : g ∈ normalizer (Q : Set X) := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn⟩
    have : IsSimpleGroup X := S.theorem1_unconditional.1
    have := hnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Q with hbot | htop'
    · exact hd.adm.ne_bot hbot
    · apply h.1
      rw [eq_top_iff, ← htop']
      exact hQM
  have hNM : ¬ normalizer (Q : Set X) ≤ M := fun hle => htM (hle htN)
  have hne : (Z ∩ ((normalizer (Q : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty :=
    ⟨z, hzZ, Subgroup.mem_inf.mpr ⟨hzN, hzM⟩⟩
  set N : Subgroup X := normalizer (Q : Set X) with hN
  set L : Subgroup X := zHull Z N with hL
  set O₁ : Subgroup X := pPrimeCoreIn L with hO₁
  set M₂ : Subgroup X := stage2M2 Z M Q with hM₂
  have hOL : O₁ ≤ L := pPrimeCoreIn_le L
  have hLO : L ≤ normalizer (O₁ : Set X) := pPrimeCoreIn_normalizes L
  have hLN : L ≤ N := (Subgroup.closure_le _).mpr Set.inter_subset_right
  have hTL : Z ∩ ((M ⊓ L : Subgroup X) : Set X) ⊆ (L : Set X) := fun x hx =>
    (Subgroup.mem_inf.mp hx.2).2
  have hT : ∀ a ∈ Z ∩ ((M ⊓ L : Subgroup X) : Set X), ∀ b ∈ Z ∩ ((M ⊓ L : Subgroup X) : Set X),
      a * b * a⁻¹ * b⁻¹ ∈ O₁ := by
    rintro a ⟨haZ, haML⟩ b ⟨hbZ, hbML⟩
    exact S.comm_mem_pPrimeCoreIn_zHull hNtop hNM hne h2rank haML hbML
      (hZ.mul_self_eq_one haZ) (hZ.mul_self_eq_one hbZ)
  have hT2 : ∀ a ∈ Z ∩ ((M ⊓ L : Subgroup X) : Set X), a * a ∈ O₁ := fun a ha => by
    rw [hZ.mul_self_eq_one ha.1]
    exact O₁.one_mem
  have hM₂def : M₂ = O₁ ⊔ Subgroup.closure (Z ∩ ((M ⊓ L : Subgroup X) : Set X)) := rfl
  have hcomm2 : ∀ x ∈ M₂, ∀ y ∈ M₂, x * y * x⁻¹ * y⁻¹ ∈ O₁ := fun x hx y hy =>
    comm_mem_of_mem_sup_closure hOL hTL hLO hT hx hy
  have hsq2 : ∀ x ∈ M₂, x * x ∈ O₁ := fun x hx =>
    mul_self_mem_of_mem_sup_closure hOL hTL hLO hT hT2 hx
  have hOM₂ : O₁ ≤ M₂ := le_sup_left
  have hM₂L : M₂ ≤ L := sup_le hOL ((Subgroup.closure_le _).mpr hTL)
  have hM₂O : M₂ ≤ normalizer (O₁ : Set X) := hM₂L.trans hLO
  have hO₁M : O₁ ≤ M := (h7E.trans (inf_le_left.trans inf_le_left))
  have hM₂ML : M₂ ≤ M ⊓ L := by
    refine le_inf (sup_le hO₁M ?_) hM₂L
    exact (Subgroup.closure_le _).mpr fun x hx => (Subgroup.mem_inf.mp hx.2).1
  have hodd₁ : Odd (Nat.card O₁) := odd_card_pPrimeCoreIn L
  have hzL : z ∈ L := Subgroup.subset_closure ⟨hzZ, hzN⟩
  have hzM₂ : z ∈ M₂ :=
    Subgroup.mem_sup_right (Subgroup.subset_closure ⟨hzZ, Subgroup.mem_inf.mpr ⟨hzM, hzL⟩⟩)
  have hM₁n : ∀ g ∈ M ⊓ L, g ∈ normalizer (M₂ : Set X) := by
    intro g hg
    refine mem_normalizer_sup_of_mem_normalizer (hLO (Subgroup.mem_inf.mp hg).2) ?_
    exact mem_normalizer_zHull_of_mem_normalizer hZ (Subgroup.le_normalizer hg)
  have hRN : R ≤ N := hd.R_syl.le.trans inf_le_right
  have hRM : R ≤ M := hd.R_syl.le.trans (inf_le_left.trans inf_le_left)
  have hRnL : R ≤ normalizer (L : Set X) := hRN.trans (le_normalizer_zHull hZ N)
  have hRnO : R ≤ normalizer (O₁ : Set X) := fun g hg => mem_normalizer_pPrimeCoreIn (hRnL hg)
  have hRnML : R ≤ normalizer ((M ⊓ L : Subgroup X) : Set X) := fun g hg =>
    mem_normalizer_inf_of_mem_normalizer (Subgroup.le_normalizer (hRM hg)) (hRnL hg)
  have hRnM₂ : R ≤ normalizer (M₂ : Set X) := fun g hg =>
    mem_normalizer_sup_of_mem_normalizer (hRnO hg)
      (mem_normalizer_zHull_of_mem_normalizer hZ (hRnML hg))
  have hRp : IsPGroup p R := hd.R_syl.isPGroup
  have hP₁n : P₁ ≤ normalizer (O₁ : Set X) := fun g hg =>
    mem_normalizer_pPrimeCoreIn ((le_normalizer_zHull hZ N) (hd.P₁_le_N hg))
  have hA₁n : O₁ ⊔ P₁ ≤ normalizer (O₁ : Set X) := sup_le Subgroup.le_normalizer hP₁n
  have hP₁A₁ : ABGLocalTools.IsSylowOf p P₁ (O₁ ⊔ P₁) :=
    hd.P₁_syl.of_le le_sup_right (sup_le h7E hd.P₁_syl.le)
  have hP₀ : ABGLocalTools.IsSylowOf p (P₁ ⊓ O₁) O₁ :=
    hP₁A₁.inf_of_le_normalizer le_sup_left hA₁n
  have hindex : ¬ p ∣ O₁.relIndex M₂ :=
    not_dvd_relIndex_of_mul_self_mem hp hp2 hOM₂ hM₂O hsq2
  have hRsyl : ABGLocalTools.IsSylowOf p R (M₂ ⊔ R) :=
    isSylowOf_sup_of_le_normalizer hOM₂ hindex hRnM₂ hRp hP₀ (inf_le_left.trans hd.P₁_le_R)
  have hsolv2 : Group.IsSolvable ↥M₂ := isSolvable_of_mul_self_mem hOM₂ hM₂O hodd₁ hsq2
  have hab2 : CFSG.BenderSuzuki.HasAbelianSylow 2 ↥M₂ :=
    hasAbelianSylow_two_of_comm_mem hOM₂ hM₂O hodd₁ hcomm2
  have hsolv : Group.IsSolvable ↥(M₂ ⊔ R) := isSolvable_sup hRnM₂ hRp hsolv2
  have hab : CFSG.BenderSuzuki.HasAbelianSylow 2 ↥(M₂ ⊔ R) :=
    hasAbelianSylow_two_sup hp2 hRnM₂ hRp hab2
  have hQD : Q ≤ M ⊓ β ⊓ N := le_inf (hd.adm.le_E.trans inf_le_left) Subgroup.le_normalizer
  have hQR : Q ≤ R :=
    le_of_isSylowOf_of_isPGroup_normal hd.R_syl hQD inf_le_right hd.adm.pgroup
  have hMhatN : M₂ ⊔ R ≤ N := sup_le (hM₂L.trans hLN) hRN
  have hQH : Q ≤ M₂ ⊔ R := hQR.trans le_sup_right
  have hcore : pCore p ↥(M₂ ⊔ R) ≠ ⊥ := by
    have hnorm : (Q.subgroupOf (M₂ ⊔ R)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hMhatN
    have hQHp : IsPGroup p ↥(Q.subgroupOf (M₂ ⊔ R)) :=
      hd.adm.pgroup.comap_subtype (K := M₂ ⊔ R)
    have hle : Q.subgroupOf (M₂ ⊔ R) ≤ pCore p ↥(M₂ ⊔ R) := le_sSup ⟨hnorm, hQHp⟩
    intro hbot
    rw [hbot, le_bot_iff] at hle
    apply hd.adm.ne_bot
    rw [← Subgroup.map_subgroupOf_eq_of_le hQH, hle, Subgroup.map_bot]
  set A : Subgroup X := (pPrimeCore p ↥M₂).map M₂.subtype with hA
  have hAeq : (pPrimeCore p ↥(M₂ ⊔ R)).map (M₂ ⊔ R).subtype = A :=
    pPrimeCore_map_sup_eq_of_le_normalizer M₂ R hRnM₂ hRp
  have hAM₂ : A ≤ M₂ := Subgroup.map_subtype_le _
  have hMn : M₂ ≤ normalizer (A : Set X) :=
    Subgroup.le_normalizer.trans
      (section8_normalizer_map_subtype_le_of_characteristic (H := M₂) (K := pPrimeCore p ↥M₂))
  have hRnA : R ≤ normalizer (A : Set X) := fun g hg =>
    section8_normalizer_map_subtype_le_of_characteristic (H := M₂) (K := pPrimeCore p ↥M₂)
      (hRnM₂ hg)
  have hAn : M₂ ⊔ R ≤ normalizer (A : Set X) := sup_le hMn hRnA
  have hM₁A : ∀ g ∈ M ⊓ L, g ∈ normalizer (A : Set X) := fun g hg =>
    section8_normalizer_map_subtype_le_of_characteristic (H := M₂) (K := pPrimeCore p ↥M₂)
      (hM₁n g hg)
  have hcopA : Nat.Coprime p (Nat.card A) := by
    rw [hA, Subgroup.card_map_of_injective M₂.subtype_injective]
    exact pPrimeCore_coprime_card (p := p) (G := ↥M₂)
  have hzA : z ∉ A := by
    intro hzA
    have hP₁H : P₁ ≤ M₂ ⊔ R := hd.P₁_le_R.trans le_sup_right
    have hcommle : ⁅zpowers z, P₁⁆ ≤ A := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg₁
      have hzk : z ^ k ∈ A := A.zpow_mem hzA k
      have h1 : g₂ * (z ^ k)⁻¹ * g₂⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hAn (hP₁H hg₂)) _).mp (A.inv_mem hzk)
      rw [commutatorElement_def]
      have e : z ^ k * g₂ * (z ^ k)⁻¹ * g₂⁻¹ = z ^ k * (g₂ * (z ^ k)⁻¹ * g₂⁻¹) := by group
      rw [e]
      exact A.mul_mem hzk h1
    have hdvd := hd.sevenD P₁ hd.P₁_syl
    have hdvd2 : Nat.card ↥⁅zpowers z, P₁⁆ ∣ Nat.card A := Subgroup.card_dvd_of_le hcommle
    exact (hp.coprime_iff_not_dvd.mp hcopA) (hdvd.trans hdvd2)
  have hoddA : Odd (Nat.card A) := by
    by_contra hnodd
    have h2 : 2 ∣ Nat.card A := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnodd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 2 h2
    have hyA : (y : X) ∈ A := y.2
    have hy2 : orderOf (y : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
    have hyML : (y : X) ∈ M ⊓ L := hM₂ML (hAM₂ hyA)
    have hzML : z ∈ M ⊓ L := Subgroup.mem_inf.mpr ⟨hzM, hzL⟩
    obtain ⟨g, hg, hgy⟩ :=
      S.exists_conj_of_involutions_zHull hNtop hNM hne hyML hzML hy2 (hZ.1 z hzZ)
    have hgA : g⁻¹ ∈ normalizer (A : Set X) := (normalizer (A : Set X)).inv_mem (hM₁A g hg)
    have h3 : g⁻¹ * (y : X) * g⁻¹⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgA _).mp hyA
    rw [inv_inv, hgy] at h3
    exact hzA h3
  obtain ⟨a, haA', n, hn, hmn⟩ :=
    exists_mul_mem_normalizer_zjSubgroup_of_solvable hp hp2 hsolv hab hRsyl hcore
      (Subgroup.mem_sup_left hm)
  rw [hAeq] at haA'
  have haM₂ : a ∈ M₂ := hAM₂ haA'
  have hnM₂ : n ∈ M₂ := by
    have hna : n = a⁻¹ * m := by rw [hmn]; group
    rw [hna]
    exact M₂.mul_mem (M₂.inv_mem haM₂) hm
  refine ⟨a, ?_, ?_, n, Subgroup.mem_inf.mpr ⟨hnM₂, (Subgroup.mem_inf.mp hn).2⟩, hmn⟩
  · exact Section7Theta.le_oPrimePrime_of_le_normalizer hAM₂ hMn hoddA hcopA haA'
  · exact le_of_odd_of_mul_self_mem hsq2 hAM₂ hoddA haA'

end CFSG.GH74.Uniqueness
