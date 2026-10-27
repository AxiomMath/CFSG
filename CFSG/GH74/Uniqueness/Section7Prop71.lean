module

public import CFSG.GH74.Uniqueness.Section7Stage2Defs
public import CFSG.GH74.Uniqueness.Theorem2
public import CFSG.GH74.Uniqueness.Section6ZJ

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem exists_conj_mem_of_factor {K O H : Subgroup X} (hOK : O ≤ K)
    (hKO : K ≤ normalizer (O : Set X)) (hHK : H ≤ K) (hodd : Odd (Nat.card O))
    (hfac : ∀ m ∈ K, ∃ a ∈ O, ∃ n ∈ H, m = a * n) {z : X} (hzK : z ∈ K) (hz : orderOf z = 2) :
    ∃ a ∈ O, a⁻¹ * z * a ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hindex : ¬ 2 ∣ H.relIndex K := by
    have hN : (O.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOK).mpr hKO
    have hsup : O.subgroupOf K ⊔ H.subgroupOf K = ⊤ := by
      rw [eq_top_iff]
      intro m _
      obtain ⟨a, ha, n, hn, hmn⟩ := hfac m m.2
      have hm : m = (⟨a, hOK ha⟩ : K) * ⟨n, hHK hn⟩ := Subtype.ext hmn
      rw [hm]
      exact Subgroup.mul_mem_sup (show (⟨a, hOK ha⟩ : K) ∈ O.subgroupOf K from ha)
        (show (⟨n, hHK hn⟩ : K) ∈ H.subgroupOf K from hn)
    have h1 := ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (O.subgroupOf K) (H.subgroupOf K)
    rw [hsup, Subgroup.relIndex_top_right] at h1
    have h2 : (H.subgroupOf K).relIndex (O.subgroupOf K) ∣ Nat.card (O.subgroupOf K) :=
      Subgroup.relIndex_dvd_card _ _
    have h3 : Nat.card (O.subgroupOf K) = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOK).toEquiv
    rw [← h1, h3] at h2
    intro h2dvd
    have : 2 ∣ Nat.card O := h2dvd.trans h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  obtain ⟨T, hT⟩ := ABGLocalTools.exists_isSylowOf 2 H
  have hTK : ABGLocalTools.IsSylowOf 2 T K := by
    rw [ABGLocalTools.isSylowOf_iff] at hT ⊢
    obtain ⟨hTH, hTp, hTidx⟩ := hT
    refine ⟨hTH.trans hHK, hTp, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex T H K hTH hHK]
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h | h
    · exact hTidx h
    · exact hindex h
  have hzp : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨S₁, hS₁, hzS₁⟩ :=
    exists_isSylowOf_ge (p := 2) (K := K) (P := zpowers z) (zpowers_le.mpr hzK) hzp
  obtain ⟨w, hwK, hw⟩ := exists_conj_of_isSylowOf hTK hS₁
  have hzS : z ∈ conjugate T w := hw ▸ hzS₁ (mem_zpowers z)
  have hwz : w * z * w⁻¹ ∈ H := hT.le (mem_conjugate_iff.mp hzS)
  obtain ⟨a, ha, n, hn, hy⟩ := hfac w⁻¹ (K.inv_mem hwK)
  refine ⟨a, ha, ?_⟩
  have hw' : w = n⁻¹ * a⁻¹ := by
    have : w = (w⁻¹)⁻¹ := (inv_inv w).symm
    rw [this, hy, mul_inv_rev]
  have : a⁻¹ * z * a = n * (w * z * w⁻¹) * n⁻¹ := by
    rw [hw']
    group
  rw [this]
  exact H.mul_mem (H.mul_mem hn hwz) (H.inv_mem hn)

variable {Z : Set X} {M : Subgroup X}

theorem stage2_contradiction (hZ : IsInvariantInvolutionSet Z) (h64 : Cor64Stmt Z M)
    {z : X} {p : ℕ} {W β Q : Subgroup X} {t : X} {R P₁ : Subgroup X}
    (hd : Stage2Data Z M z p W β Q t R P₁)
    (h7E : pPrimeCoreIn (zHull Z (normalizer (Q : Set X))) ≤ stage2E M β z)
    (h711 : ∀ m ∈ stage2M2 Z M Q, ∃ a ∈ oPrimePrime p (stage2M2 Z M Q),
      a ∈ pPrimeCoreIn (zHull Z (normalizer (Q : Set X))) ∧
        ∃ n ∈ stage2M2 Z M Q ⊓ normalizer (zjSubgroup p R : Set X), m = a * n) : False := by
  have hcand := hd.tmax.cand
  have hp : p.Prime := hcand.prime
  have : Fact p.Prime := ⟨hp⟩
  have hzZ : z ∈ Z := hcand.mem_Z
  have hzN : z ∈ normalizer (Q : Set X) := hd.adm.z_norm
  have hzL : z ∈ zHull Z (normalizer (Q : Set X)) := Subgroup.subset_closure ⟨hzZ, hzN⟩
  have hzM₂ : z ∈ stage2M2 Z M Q :=
    Subgroup.mem_sup_right (Subgroup.subset_closure ⟨hzZ, Subgroup.mem_inf.mpr ⟨hcand.mem_M, hzL⟩⟩)
  have hOM₂ : pPrimeCoreIn (zHull Z (normalizer (Q : Set X))) ≤ stage2M2 Z M Q := le_sup_left
  have hM₂L : stage2M2 Z M Q ≤ zHull Z (normalizer (Q : Set X)) := by
    refine sup_le (pPrimeCoreIn_le _) ?_
    exact ((Subgroup.closure_le _).mpr Set.inter_subset_right :
      zHull Z (M ⊓ zHull Z (normalizer (Q : Set X))) ≤ M ⊓ zHull Z (normalizer (Q : Set X))).trans
        inf_le_right
  have hM₂O := hM₂L.trans (pPrimeCoreIn_normalizes (zHull Z (normalizer (Q : Set X))))
  have hHM₂ : stage2M2 Z M Q ⊓ normalizer (zjSubgroup p R : Set X) ≤ stage2M2 Z M Q := inf_le_left
  have hfac : ∀ m ∈ stage2M2 Z M Q,
      ∃ a ∈ pPrimeCoreIn (zHull Z (normalizer (Q : Set X))),
        ∃ n ∈ stage2M2 Z M Q ⊓ normalizer (zjSubgroup p R : Set X), m = a * n := by
    intro m hm
    obtain ⟨a, -, haO, n, hn, hmn⟩ := h711 m hm
    exact ⟨a, haO, n, hn, hmn⟩
  obtain ⟨a, haO, ha⟩ := exists_conj_mem_of_factor hOM₂ hM₂O hHM₂
    (odd_card_pPrimeCoreIn _) hfac hzM₂ (hZ.1 z hzZ)
  have haN : a⁻¹ * z * a ∈ normalizer (zjSubgroup p R : Set X) := (Subgroup.mem_inf.mp ha).2
  have hxO : a⁻¹ ∈ pPrimeCoreIn (zHull Z (normalizer (Q : Set X))) := Subgroup.inv_mem _ haO
  obtain ⟨x, hx⟩ : ∃ x : X, x = a⁻¹ := ⟨_, rfl⟩
  rw [← hx] at hxO
  have hxE : x ∈ stage2E M β z := h7E hxO
  have hxD : x ∈ M ⊓ β := (Subgroup.mem_inf.mp hxE).1
  have hxM : x ∈ M := (Subgroup.mem_inf.mp hxD).1
  have hxβ : x ∈ β := (Subgroup.mem_inf.mp hxD).2
  have hzZ₂ : z ∈ normalizer (conjugate (zjSubgroup p R) x : Set X) := by
    rw [normalizer_conjugate, mem_conjugate_iff]
    have : x * z * x⁻¹ = a⁻¹ * z * a := by rw [hx, inv_inv]
    rw [this]
    exact haN
  have hZ₂eq : conjugate (zjSubgroup p R) x = zjSubgroup p (conjugate R x) :=
    (zjSubgroup_conjugate p R x).symm
  have hD : conjugate (M ⊓ β) x = M ⊓ β :=
    conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hxD)
  have hRD : R ≤ M ⊓ β := hd.R_syl.le.trans inf_le_left
  have hR'D : conjugate R x ≤ M ⊓ β := hD ▸ conjugate_mono hRD x
  have hRp : IsPGroup p R := hd.R_syl.isPGroup
  have hR'p : IsPGroup p (conjugate R x) := isPGroup_conjugate hRp x
  have hR'card : Nat.card ↥(conjugate R x) = Nat.card R := card_conjugate R x
  have hRne : R ≠ ⊥ := by
    intro hRbot
    have h1 : Nat.card P₁ < 1 := by
      have := hd.card_P₁_lt
      rwa [hRbot, Subgroup.card_bot] at this
    exact absurd h1 (not_lt.mpr Nat.card_pos)
  have hR'ne : conjugate R x ≠ ⊥ := by
    intro hbot
    apply hRne
    have := hR'card
    rw [hbot, Subgroup.card_bot] at this
    exact Subgroup.card_eq_one.mp this.symm
  have hNN : normalizer (conjugate R x : Set X) ≤
      normalizer (conjugate (zjSubgroup p R) x : Set X) := by
    rw [hZ₂eq]
    exact normalizer_le_normalizer_zjSubgroup p hp _
  have hxMinv : conjugate M x⁻¹ = M :=
    conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (M.inv_mem hxM))
  have hβx : conjugate β x = β :=
    conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hxβ)
  have hadm : Stage2Adm Z M z p β (conjugate (zjSubgroup p R) x) := by
    refine ⟨?_, ?_, ?_, hzZ₂, ?_⟩
    · rw [hZ₂eq]
      exact zjSubgroup_ne_bot p hp hR'p hR'ne
    · rw [hZ₂eq]
      exact hR'p.to_le (zjSubgroup_le p _)
    · rw [hZ₂eq] at hzZ₂ ⊢
      exact prop38a (M := M) ((zjSubgroup_le p _).trans hR'D) hzZ₂
    · refine ⟨x⁻¹ * t * x, hZ.2 t hd.t_mem x, ?_, ?_, conjugate P₁ x, ?_, ?_, ?_⟩
      · refine hNN ?_
        rw [normalizer_conjugate, mem_conjugate_iff]
        have : x * (x⁻¹ * t * x) * x⁻¹ = t := by group
        rw [this]
        exact hd.t_norm_R
      · calc conjugate M (x⁻¹ * t * x) = conjugate (conjugate (conjugate M x⁻¹) t) x := by
              rw [conjugate_conjugate, conjugate_conjugate, mul_assoc]
          _ = β := by rw [hxMinv, hd.t_swap, hβx]
      · exact isSylowOf_conjugate_of_mem hd.P₁_syl hxE
      · refine le_trans (conjugate_mono hd.P₁_le_R x) ?_
        exact (Subgroup.le_normalizer (H := conjugate R x)).trans hNN
      · rw [normalizer_conjugate, mem_conjugate_iff]
        have : x * (x⁻¹ * t * x) * x⁻¹ = t := by group
        rw [this]
        exact hd.t_norm_P₁
  have hmax := hd.maxQ _ hadm
  have hRcard : Nat.card R = p ^ stage2NDExp p M β Q := hd.R_syl.card_eq
  have hR'ND : conjugate R x ≤
      M ⊓ β ⊓ normalizer (conjugate (zjSubgroup p R) x : Set X) :=
    le_inf hR'D (Subgroup.le_normalizer.trans hNN)
  obtain ⟨S, hS, hR'S⟩ := exists_isSylowOf_ge (p := p) hR'ND hR'p
  have hScard : Nat.card S = p ^ stage2NDExp p M β (conjugate (zjSubgroup p R) x) := hS.card_eq
  have hSle : Nat.card S ≤ Nat.card ↥(conjugate R x) := by
    rw [hScard, hR'card, hRcard]
    exact Nat.pow_le_pow_right hp.pos hmax
  have hSeq : conjugate R x = S := Subgroup.eq_of_le_of_card_ge hR'S hSle
  have hR'syl : ABGLocalTools.IsSylowOf p (conjugate R x)
      (M ⊓ β ⊓ normalizer (conjugate (zjSubgroup p R) x : Set X)) := hSeq ▸ hS
  have hR'sylD : ABGLocalTools.IsSylowOf p (conjugate R x) (M ⊓ β) := by
    by_contra hnot
    obtain ⟨S', hS', hR'S'⟩ := exists_isSylowOf_ge (p := p) hR'D hR'p
    have hlt : conjugate R x < S' := lt_of_le_of_ne hR'S' (fun heq => hnot (heq ▸ hS'))
    obtain ⟨R₁, hR₁p, hR'R₁, hR₁S', hR₁N⟩ :=
      CFSG.BenderSuzuki.exists_larger_normalizer_pSubgroup hp hS'.isPGroup hlt
    have hR₁ND : R₁ ≤ M ⊓ β ⊓ normalizer (conjugate (zjSubgroup p R) x : Set X) :=
      le_inf (hR₁S'.trans hS'.le) (hR₁N.trans hNN)
    exact hR'R₁.ne (hR'syl.eq_of_le hR'R₁.le hR₁ND hR₁p).symm
  have hzθ : z ∈ normalizer (oPrimePrime p (M ⊓ β) : Set X) := by
    rw [hd.theta]
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    simp only [Subgroup.mem_bot]
    exact conj_eq_one_iff.symm
  obtain ⟨-, h64'⟩ := h64 z p W hcand β hd.beta_mem hd.beta_ne hzθ
  refine h64' (conjugate R x) hR'D hR'p ?_ ?_
  · exact ⟨conjugate R x ⊓ pPrimeCoreIn (M ⊓ β),
      hR'sylD.inf_of_le_normalizer (pPrimeCoreIn_le _) (pPrimeCoreIn_normalizes _), inf_le_left⟩
  · rw [← hZ₂eq]
    exact hzZ₂

theorem prop71_of_stage2 (hZ : IsInvariantInvolutionSet Z) (hEx : Stage2ExistsStmt Z M)
    (h710 : Lemma710Stmt Z M) (h711 : Lemma711Stmt Z M) (h64 : Cor64Stmt Z M) :
    Prop71Stmt Z M := by
  intro z p W hmax
  exfalso
  obtain ⟨β, Q, t, R, P₁, hd⟩ := hEx z p W hmax
  obtain ⟨h2, h7E⟩ := h710 z p W β Q t R P₁ hd
  exact stage2_contradiction hZ h64 hd h7E (h711 z p W β Q t R P₁ hd h2 h7E)

end CFSG.GH74.Uniqueness
