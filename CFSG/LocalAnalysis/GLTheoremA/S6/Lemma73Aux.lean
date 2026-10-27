module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma73AuxSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def L73Prod (b a : G) (M K J : Subgroup G) : Prop :=
  GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) M ∧ GLBConj b M ≠ M ∧
    GLBConj b (GLBConj b M) ≠ M ∧ K = M ⊔ GLBConj b M ⊔ GLBConj b (GLBConj b M) ∧
    b ∈ Subgroup.centralizer ({a} : Set G) ∧ b ^ 3 = 1 ∧ J ≤ K ∧
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J

theorem not_isPGroup_two_of_isAltPType {I : Subgroup G} {m : ℕ} (hm : 5 ≤ m) (h : IsAltPType 3 I m) :
    ¬ IsPGroup 2 I := by
  intro hI
  obtain ⟨e⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (PQuot 3 I) := hI.to_quotient (GLAPPrimeCore 3 ↥I)
  have hA : IsPGroup 2 ↥(alternatingGroup (Fin m)) := hQ.of_equiv e
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hA
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h3 : 3 ∣ Nat.card ↥(alternatingGroup (Fin m)) := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    have h6 : 3 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h2 : m.factorial = 2 * (m.factorial / 2) := by
      have : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      omega
    rw [h2] at h6
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h6)
  rw [hk] at h3
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem l73_exists_a (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (S : AltSetup 3 B x L n y J) {T I : Subgroup G} (hTI : L73TI B x L n y J T I) :
    ∃ a : G, a ∈ altDxy x y ∧ a ≠ 1 ∧
      (⁅I, Subgroup.centralizer ({a} : Set G) ⊓ pCoreOf 2 (Subgroup.normalizer (T : Set G))⁆ :
        Subgroup G) ≠ ⊥ := by
  have hT0 : T ≠ ⊥ := by
    rintro rfl
    exact hTI.T_not_le bot_le
  have hIX : I ≤ Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓ L := by
    rw [hTI.I_eq]
    exact sSup_le fun K hK => hK.1
  have hIND : I ≤ Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer (altDxy x y : Set G) :=
    hIX.trans inf_le_left
  have hD0 : altDxy x y ≠ ⊥ := by
    intro h
    have := S.card_D
    rw [h, Subgroup.card_bot] at this
    have h1 : 1 < 3 ^ 2 := by norm_num
    omega
  obtain ⟨A, hAD, hAi, hne⟩ := GL83.I_33_3_proved G hc.charTwo 3 hc.prime hc.odd
    (Subgroup.normalizer (T : Set G)) (altDxy x y) I ⟨T, hT0, hTI.T_two, rfl⟩ hD0 S.isElemAbelian_D
    hTI.D_le_N hIND (not_isPGroup_two_of_isAltPType (m := n - 4) (by have := S.three_mul_le; omega) hTI.I_alt)
  obtain ⟨a, haA, ha1, rfl⟩ := exists_gen_of_index hc.prime S.card_D hAD hAi
  refine ⟨a, hAD haA, ha1, ?_⟩
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, inf_comm] at hne

private theorem y5x_centralizer_eq_inf {D : Subgroup G} {a b : G}
    (hD : D = Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
  rw [hD, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
    Subgroup.centralizer_closure]
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_union,
    Set.mem_singleton_iff, or_imp, forall_and, forall_eq]

private theorem y5x_closureIn_eq_iSup (I H : Subgroup G) :
    closureIn I H = ⨆ g ∈ H, GLBConj g I := by
  unfold closureIn
  apply le_antisymm
  · refine iSup₂_le fun a ha => ?_
    have : I.map (MulAut.conj a).toMonoidHom = GLBConj a⁻¹ I := by
      unfold GLBConj
      rw [inv_inv]
    rw [this]
    exact le_iSup₂_of_le a⁻¹ (H.inv_mem ha) le_rfl
  · refine iSup₂_le fun g hg => ?_
    unfold GLBConj
    exact le_iSup₂_of_le g⁻¹ (H.inv_mem hg) le_rfl

theorem l73_shape (hc : S6Ctx G 3) (i183 : Input18_3_4) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ}
    {y : G} {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) {a : G}
    (haD : a ∈ altDxy x y) (ha1 : a ≠ 1) : L72Single 3 (altDxy x y) J (closureIn J (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)))) a ∨ ∃ (b : G) (M : Subgroup G), b ∈ (altDxy x y) ∧ b ∉ Subgroup.zpowers a ∧ L73Prod b a M (closureIn J (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)))) J := by
  classical
  obtain ⟨b, hbD, hb, hDab⟩ := exists_pair_of_card_sq hc.prime S.card_D haD ha1 S.isElemAbelian_D
  have hJab : GLAPComponent 3
      (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G)) J := by
    have hJD := l72_pComponent_centralizer hc.prime hB S
    rwa [y5x_centralizer_eq_inf hDab] at hJD
  have hKa : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) := kGroup_centralizer hc ha1
  have hab : a * b = b * a := isElemAbelian_commute S.isElemAbelian_D haD hbD
  have hbN : Subgroup.zpowers b ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hab.symm)
  have hbel : IsElemAbelian 3 (Subgroup.zpowers b) :=
    isElemAbelian_zpowers_of_mem S.isElemAbelian_D hbD
  have hJz : GLAPComponent 3 (Subgroup.centralizer ({a} : Set G) ⊓
      Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G)) J := by
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨𝒞, h𝒞c, h𝒞sup, h𝒞inv, h𝒞tr⟩ := i183 G (Subgroup.centralizer ({a} : Set G)) hKa 3 hc.prime
    (Subgroup.zpowers b) hbN hbel J hJz
  have hKsup : closureIn J (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G))) = ⨆ M ∈ 𝒞, M := by
    rw [y5x_closureIn_eq_iSup, h𝒞sup]
  have hKa' : closureIn J (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G))) ≤
      Subgroup.centralizer ({a} : Set G) := by
    rw [hKsup]
    exact iSup₂_le fun M hM => (h𝒞c M hM).1
  have hJK : J ≤ closureIn J (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G))) :=
    le_closureIn_self J _
  have hJb : J ≤ Subgroup.centralizer ({b} : Set G) := hJab.1.trans inf_le_right
  have hb3 : b ^ 3 = 1 := S.isElemAbelian_D.2 b hbD
  by_cases hfix : ∀ M ∈ 𝒞, GLBConj b M = M
  ·
    have hone : ∀ M ∈ 𝒞, ∀ M' ∈ 𝒞, M = M' := by
      intro M hM M' hM'
      obtain ⟨e, he, rfl⟩ := h𝒞tr M hM M' hM'
      have hbn : b ∈ Subgroup.normalizer (M : Set G) := mem_normalizer_iff_gLBConj_eq.2 (hfix M hM)
      exact (mem_normalizer_iff_gLBConj_eq.1 (Subgroup.zpowers_le.2 hbn he)).symm
    exact Or.inl (l72_single_of_family hc.prime hDab hJab h𝒞c h𝒞sup h𝒞inv hone)
  ·
    push Not at hfix
    obtain ⟨M, hM, hMb⟩ := hfix
    have hbM1 : GLBConj b M ∈ 𝒞 := h𝒞inv M hM b (Subgroup.mem_zpowers b)
    have hbM2mem : GLBConj b (GLBConj b M) ∈ 𝒞 := h𝒞inv _ hbM1 b (Subgroup.mem_zpowers b)
    have hbbb : b * (b * b) = 1 := by
      rw [← pow_three, hb3]
    have hb3z : b ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hb3]
    have hcube : ∀ k : ℤ, GLBConj (b ^ k) M = M ∨ GLBConj (b ^ k) M = GLBConj b M ∨
        GLBConj (b ^ k) M = GLBConj b (GLBConj b M) := by
      intro k
      have hk : b ^ k = b ^ (k % 3) := by
        conv_lhs => rw [← Int.mul_ediv_add_emod k 3]
        rw [zpow_add, zpow_mul, hb3z, one_zpow, one_mul]
      have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rw [hk]
      rcases hr with h | h | h <;> rw [h]
      · exact Or.inl (by simp [gLBConj_one])
      · exact Or.inr (Or.inl (by simp))
      · refine Or.inr (Or.inr ?_)
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two,
          gLBConj_gLBConj]
    have hmem : ∀ L ∈ 𝒞, L = M ∨ L = GLBConj b M ∨ L = GLBConj b (GLBConj b M) := by
      intro L hL
      obtain ⟨e, he, rfl⟩ := h𝒞tr M hM L hL
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      exact hcube k
    have hbM2 : GLBConj b (GLBConj b (GLBConj b M)) = M := by
      rw [gLBConj_gLBConj, gLBConj_gLBConj, hbbb, gLBConj_one]
    have hM2M : GLBConj b (GLBConj b M) ≠ M := by
      intro h
      apply hMb
      have h1 : GLBConj b (GLBConj b (GLBConj b M)) = GLBConj b M := by rw [h]
      rw [hbM2] at h1
      exact h1.symm
    have hK3 : closureIn J (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G))) =
        M ⊔ GLBConj b M ⊔ GLBConj b (GLBConj b M) := by
      rw [hKsup]
      apply le_antisymm
      · refine iSup₂_le fun L hL => ?_
        rcases hmem L hL with h | h | h <;> rw [h]
        · exact le_sup_of_le_left le_sup_left
        · exact le_sup_of_le_left le_sup_right
        · exact le_sup_right
      · exact sup_le (sup_le (le_iSup₂_of_le M hM le_rfl) (le_iSup₂_of_le _ hbM1 le_rfl))
          (le_iSup₂_of_le _ hbM2mem le_rfl)
    have hJcomp : GLAPComponent 3 (closureIn J (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G))) ⊓
        Subgroup.centralizer ({b} : Set G)) J :=
      glaPComponent_of_le hc.prime hJab (le_inf hJK hJb) (inf_le_inf_right _ hKa')
    refine Or.inr ⟨b, M, hbD, hb, ?_⟩
    unfold L73Prod
    exact ⟨h𝒞c M hM, hMb, hM2M, hK3, hbN (Subgroup.mem_zpowers b), hb3, hJK, hJcomp⟩

private theorem y5x_kSub_conj_mem {I H : Subgroup G} {g z : G} (hg : g ∈ H)
    (hz : z ∈ closureIn I H) : g * z * g⁻¹ ∈ closureIn I H := by
  rw [closureIn_eq_iSup_gLBConj] at hz ⊢
  have key : (⨆ h ∈ H, GLBConj h I) ≤
      (⨆ h ∈ H, GLBConj h I).comap (MulAut.conj g).toMonoidHom := by
    refine iSup₂_le fun h hh => ?_
    intro w hw
    have hw' : h * w * h⁻¹ ∈ I := CFSG.LocalAnalysis.GLTheoremB.mem_gLBConj.1 hw
    have hmem : g * w * g⁻¹ ∈ GLBConj (h * g⁻¹) I := by
      rw [CFSG.LocalAnalysis.GLTheoremB.mem_gLBConj]
      have e : h * g⁻¹ * (g * w * g⁻¹) * (h * g⁻¹)⁻¹ = h * w * h⁻¹ := by group
      rw [e]
      exact hw'
    exact le_biSup (fun k => GLBConj k I) (H.mul_mem hh (H.inv_mem hg)) hmem
  exact Subgroup.mem_comap.1 (key hz)

theorem l73_K_sub (hc : S6Ctx G 3) (i183 : Input18_3_4) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) {a : G}
    (haD : a ∈ altDxy x y) (ha1 : a ≠ 1) {K : Subgroup G}
    (hK : K = closureIn J (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)))) :
    IsSubnormal K (Subgroup.centralizer ({a} : Set G)) := by
  subst hK
  have hp : Nat.Prime 3 := hc.prime
  have hDa : altDxy x y ≤ Subgroup.centralizer ({a} : Set G) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute S.isElemAbelian_D haD hd).symm
  have hCDa : Subgroup.centralizer (altDxy x y : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD)
  have hJ : GLAPComponent 3 (Subgroup.centralizer ({a} : Set G) ⊓
      Subgroup.centralizer (altDxy x y : Set G)) J := by
    rw [inf_eq_right.2 hCDa]
    exact l72_pComponent_centralizer hp hB S
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, -⟩ :=
    i183 G (Subgroup.centralizer ({a} : Set G)) (kGroup_centralizer hc ha1) 3 hp (altDxy x y) hDa
      S.isElemAbelian_D J hJ
  have hKeq : closureIn J (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G))) = ⨆ M ∈ 𝒞, M := by
    rw [closureIn_eq_iSup_gLBConj, h𝒞sup]
  have hKle : closureIn J (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G))) ≤
      GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)) := by
    rw [hKeq]
    exact iSup₂_le fun M hM => le_sSup (h𝒞c M hM)
  have hKN : GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)) ≤
      Subgroup.normalizer (closureIn J (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G))) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact y5x_kSub_conj_mem (I := J) hg hz
    · intro hz
      have h := y5x_kSub_conj_mem (I := J) (Subgroup.inv_mem _ hg) hz
      have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
      rwa [e] at h
  have hLaC : GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)) ≤ Subgroup.centralizer ({a} : Set G) :=
    sSup_le fun M hM => hM.1
  have hCN : Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    fun g hg => mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)
  exact IsSubnormal.trans
    (IsSubnormal.step hKle ((Subgroup.normal_subgroupOf_iff_le_normalizer hKle).2 hKN)
      (IsSubnormal.refl _))
    (IsSubnormal.step hLaC ((Subgroup.normal_subgroupOf_iff_le_normalizer hLaC).2 hCN)
      (IsSubnormal.refl _))

theorem l73_norm_S {x y : G} {L T I : Subgroup G}
    (hIeq : I = GLAPLayer 3 (Subgroup.normalizer (T : Set G) ⊓
      Subgroup.centralizer (altDxy x y : Set G) ⊓ L)) {a : G} (haD : a ∈ altDxy x y) {A : Subgroup G}
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hAD : A ≤ Subgroup.centralizer (altDxy x y : Set G)) :
    A ≤ Subgroup.normalizer ((⁅I, Subgroup.centralizer ({a} : Set G) ⊓
      pCoreOf 2 (Subgroup.normalizer (T : Set G))⁆ : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinf : ∀ {H K : Subgroup G} {g : G}, g ∈ Subgroup.normalizer (H : Set G) →
      g ∈ Subgroup.normalizer (K : Set G) → g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) :=
    fun {H K g} h1 h2 => by
      rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
      intro z
      exact ⟨fun hz => ⟨(h1 z).1 hz.1, (h2 z).1 hz.2⟩, fun hz => ⟨(h1 z).2 hz.1, (h2 z).2 hz.2⟩⟩
  have hAX : A ≤ Subgroup.normalizer ((Subgroup.normalizer (T : Set G) ⊓
      Subgroup.centralizer (altDxy x y : Set G) ⊓ L : Subgroup G) : Set G) := fun g hg =>
    hinf (hinf (Subgroup.le_normalizer (hAT hg)) (Subgroup.le_normalizer (hAD hg))) (hAL hg)
  have hAI : A ≤ Subgroup.normalizer (I : Set G) := fun g hg => by
    rw [hIeq]; exact mem_normalizer_glaPLayer (hAX hg)
  have haC : ∀ g ∈ A, g ∈ Subgroup.centralizer ({a} : Set G) := fun g hg =>
    Subgroup.centralizer_le (by simpa using haD) (hAD hg)
  have hAC : A ≤ Subgroup.normalizer ((Subgroup.centralizer ({a} : Set G) ⊓
      pCoreOf 2 (Subgroup.normalizer (T : Set G)) : Subgroup G) : Set G) := fun g hg =>
    hinf (Subgroup.le_normalizer (haC g hg))
      (le_normalizer_pCoreOf 2 (Subgroup.normalizer (T : Set G)) (hAT hg))
  exact le_normalizer_commutator hAI hAC

theorem altDxy_le_normalizer_L {x y : G} {L : Subgroup G} (hxL : L ≤ Subgroup.centralizer ({x} : Set G))
    (hy : y ∈ L) : altDxy x y ≤ Subgroup.normalizer (L : Set G) := by
  unfold altDxy
  refine sup_le ((Subgroup.zpowers_le).2 ?_) ((Subgroup.zpowers_le).2 (Subgroup.le_normalizer hy))
  refine Subgroup.centralizer_le_normalizer (L : Set G) (Subgroup.mem_centralizer_iff.2 fun l hl => ?_)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hxL hl)

structure L73Ctx (B : Subgroup G) (x : G) (L : Subgroup G) (n : ℕ) (y : G) (J : Subgroup G) (a : G)
    (K T I S : Subgroup G) : Prop where
  ti : L73TI B x L n y J T I
  a_mem : a ∈ altDxy x y
  a_ne : a ≠ 1
  S_eq : S = ⁅I, Subgroup.centralizer ({a} : Set G) ⊓ pCoreOf 2 (Subgroup.normalizer (T : Set G))⁆
  S_ne : S ≠ ⊥
  S_two : IsPGroup 2 S
  I_norm : I ≤ Subgroup.normalizer (S : Set G)
  D_norm : altDxy x y ≤ Subgroup.normalizer (S : Set G)
  S_comm : S ≤ ⁅S, I⁆
  S_le_Ca : S ≤ Subgroup.centralizer ({a} : Set G)
  K_eq : K = closureIn J (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)))
  J_le_K : J ≤ K
  K_sn : IsSubnormal K (Subgroup.centralizer ({a} : Set G))
  S_le_K : S ≤ K

theorem l73_ctx (hc : S6Ctx G 3) (i183 : Input18_3_4) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) (hn12 : n ≤ 12)
    (hy : n < 12 → y ∈ B) :
    ∃ (T I : Subgroup G) (a : G) (K Sg : Subgroup G), L73Ctx B x L n y J a K T I Sg := by
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := (IsSStarMax.component hB).1
  obtain ⟨T, I, hTI⟩ := l73_exists_TI hc hB S hn12 hy
  obtain ⟨a, haD, ha1, hSne⟩ := l73_exists_a hc S hTI
  set K := closureIn J (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G))) with hKdef
  set N := Subgroup.normalizer (T : Set G) with hNdef
  set C := Subgroup.centralizer ({a} : Set G) ⊓ pCoreOf 2 N with hCdef
  set S₀ := (⁅I, C⁆ : Subgroup G) with hS₀def
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC2 : IsPGroup 2 C :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le inf_le_right
  have hIX : I ≤ N ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓ L := by
    rw [hTI.I_eq]
    exact sSup_le fun K hK => hK.1
  have hIN : I ≤ N := hIX.trans (inf_le_left.trans inf_le_left)
  have hID : I ≤ Subgroup.centralizer (altDxy x y : Set G) :=
    hIX.trans (inf_le_left.trans inf_le_right)
  have hIa : I ≤ Subgroup.centralizer ({a} : Set G) :=
    hID.trans (Subgroup.centralizer_le (by simpa using haD))
  have hIC : I ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_gLBConj_eq, hCdef, gLBConj_inf,
      mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_pCoreOf 2 N (hIN hg)),
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hIa hg))]
  have hS₀C : S₀ ≤ C := by
    rw [hS₀def, Subgroup.commutator_comm]
    exact commutator_le_left_of_normalizes hIC
  have hS₀2 : IsPGroup 2 S₀ := hC2.to_le hS₀C
  have hS₀I : S₀ ≤ ⁅S₀, I⁆ := le_commutator_of_genByPElts hc.prime hc.odd hC2 hIC hTI.gen
  have hIS : I ≤ Subgroup.normalizer (S₀ : Set G) :=
    le_normalizer_commutator Subgroup.le_normalizer hIC
  have hS₀a : S₀ ≤ Subgroup.centralizer ({a} : Set G) := hS₀C.trans inf_le_left
  have hJK : J ≤ K := le_closureIn_self J _
  have hIK : I ≤ K := hTI.I_le_J.trans hJK
  have hKsn : IsSubnormal K (Subgroup.centralizer ({a} : Set G)) := l73_K_sub hc i183 hB S haD ha1 hKdef
  have hS₀K : S₀ ≤ K := le_of_commutator_subnormal hKsn hIK hS₀a hS₀I
  exact ⟨T, I, a, K, S₀, ⟨hTI, haD, ha1, hS₀def, hSne, hS₀2, hIS,
    l73_norm_S hTI.I_eq haD hTI.D_le_N (altDxy_le_normalizer_L hxL S.y_mem)
      (fun d hd e he => (isElemAbelian_commute S.isElemAbelian_D he hd)), hS₀I, hS₀a, hKdef, hJK, hKsn, hS₀K⟩⟩

end CFSG.LocalAnalysis.GLTheoremA
