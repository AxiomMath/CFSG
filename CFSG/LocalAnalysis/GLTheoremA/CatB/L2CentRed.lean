module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VDiag
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Main
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Proving CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem l2c_conj_mem_cent {x g h : G} (hg : g ∈ Subgroup.centralizer ({x} : Set G))
    (hh : h ∈ Subgroup.centralizer ({x} : Set G)) :
    g * h * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
  have hg' : x * g = g * x := Subgroup.mem_centralizer_iff.1 hg x (Set.mem_singleton x)
  have hh' : x * h = h * x := Subgroup.mem_centralizer_iff.1 hh x (Set.mem_singleton x)
  have h3 : g⁻¹ * x = x * g⁻¹ := by
    calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * x) * g⁻¹ := by rw [hg']
      _ = x * g⁻¹ := by group
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  rw [Set.mem_singleton_iff.1 hy]
  calc x * (g * h * g⁻¹) = (x * g) * h * g⁻¹ := by group
    _ = (g * x) * h * g⁻¹ := by rw [hg']
    _ = g * (x * h) * g⁻¹ := by group
    _ = g * (h * x) * g⁻¹ := by rw [hh']
    _ = g * h * (x * g⁻¹) := by group
    _ = g * h * (g⁻¹ * x) := by rw [h3]
    _ = g * h * g⁻¹ * x := by group

theorem l2c_conj_O {W : Subgroup G} {w o : G} (hw : w ∈ Subgroup.normalizer (W : Set G))
    (ho : o ∈ GLAPPrimeCoreOf 3 W) : w * o * w⁻¹ ∈ GLAPPrimeCoreOf 3 W := by
  have hE : GLBConj w (GLAPPrimeCoreOf 3 W) = GLAPPrimeCoreOf 3 W := by
    rw [← glaPPrimeCoreOf_gLBConj, gLBConj_eq_of_mem_normalizer hw]
  have : o ∈ GLBConj w (GLAPPrimeCoreOf 3 W) := by rw [hE]; exact ho
  exact (mem_gLBConj).1 this

theorem l2c_O_mul {W : Subgroup G} {w₁ w₂ l : G} (h₁ : w₁ ∈ W) (h₂ : w₂ ∈ W)
    (e₁ : ⁅w₁, l⁆ ∈ GLAPPrimeCoreOf 3 W) (e₂ : ⁅w₂, l⁆ ∈ GLAPPrimeCoreOf 3 W) :
    ⁅w₁ * w₂, l⁆ ∈ GLAPPrimeCoreOf 3 W := by
  rw [commutatorElement_def] at e₁ e₂ ⊢
  have key : w₁ * w₂ * l * (w₁ * w₂)⁻¹ * l⁻¹ =
      (w₁ * (w₂ * l * w₂⁻¹ * l⁻¹) * w₁⁻¹) * (w₁ * l * w₁⁻¹ * l⁻¹) := by group
  rw [key]
  exact (GLAPPrimeCoreOf 3 W).mul_mem (l2c_conj_O (Subgroup.le_normalizer h₁) e₂) e₁

theorem l2c_O_inv {W : Subgroup G} {w l : G} (h₁ : w ∈ W)
    (e₁ : ⁅w, l⁆ ∈ GLAPPrimeCoreOf 3 W) : ⁅w⁻¹, l⁆ ∈ GLAPPrimeCoreOf 3 W := by
  have key : ⁅w⁻¹, l⁆ = w⁻¹ * (⁅w, l⁆)⁻¹ * w⁻¹⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [key]
  exact l2c_conj_O (Subgroup.le_normalizer (W.inv_mem h₁)) ((GLAPPrimeCoreOf 3 W).inv_mem e₁)

def l2cZ (W L : Subgroup G) : Subgroup G where
  carrier := {w | w ∈ W ∧ ∀ l ∈ L, ⁅w, l⁆ ∈ GLAPPrimeCoreOf 3 W}
  one_mem' := ⟨W.one_mem, fun l _ => by
    rw [commutatorElement_one_left]; exact (GLAPPrimeCoreOf 3 W).one_mem⟩
  mul_mem' := fun {a b} ha hb => ⟨W.mul_mem ha.1 hb.1, fun l hl =>
    l2c_O_mul ha.1 hb.1 (ha.2 l hl) (hb.2 l hl)⟩
  inv_mem' := fun {a} ha => ⟨W.inv_mem ha.1, fun l hl => l2c_O_inv ha.1 (ha.2 l hl)⟩

theorem l2c_normal_inf {V W : Subgroup G} {x : G} (hWV : V ≤ Subgroup.normalizer (W : Set G))
    (hWV' : W ≤ V) :
    ((W ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
      (V ⊓ Subgroup.centralizer ({x} : Set G))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_inf_right _ hWV')]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  have hgW : ∀ h, h ∈ W ↔ g * h * g⁻¹ ∈ W := fun h =>
    Subgroup.mem_normalizer_iff.1 (hWV hg.1) h
  have hgC : ∀ h, h ∈ Subgroup.centralizer ({x} : Set G) ↔
      g * h * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    intro h
    refine ⟨fun hh => l2c_conj_mem_cent hg.2 hh, fun hh => ?_⟩
    have := l2c_conj_mem_cent (Subgroup.inv_mem _ hg.2) hh
    simpa [mul_assoc] using this
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hgW n, hgC n]

theorem l2c_fam_mem {Y W : Subgroup G} {𝒞 : Set (Subgroup G)} {V : Subgroup G}
    (hW : W = ⨆ M ∈ 𝒞, M) (h𝒞 : ∀ M ∈ 𝒞, GLAPComponent 3 Y M) (hWV : W ≤ V)
    (hNW : V ≤ Subgroup.normalizer (W : Set G)) {K L : Subgroup G} (hKW : K ≤ W)
    (hKlay : K ≤ GLAPLayer 3 V) (hL : GLAPComponent 3 V L)
    (hK : ¬ ⁅K, L⁆ ≤ GLAPPrimeCoreOf 3 V) : L ∈ 𝒞 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hWY : W ≤ Y := by
    rw [hW]; exact iSup₂_le fun M hM => (h𝒞 M hM).1
  have hMW : ∀ M ∈ 𝒞, GLAPComponent 3 W M := fun M hM =>
    glaPComponent_of_le hp (h𝒞 M hM)
      (by rw [hW]; exact le_iSup₂ (f := fun M (_ : M ∈ 𝒞) => M) M hM) hWY
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := fun k hk =>
    i183_glaPLayer_le_normalizer hp hL (hKlay hk)
  have hLW : L ≤ W := by
    refine i183_le_of_commutator hL (hKW.trans hWV) hKN ?_ ?_ hK
    · exact fun l hl => hNW (hL.1 hl)
    · refine Subgroup.commutator_le.2 fun k hk l hl => ?_
      rw [commutatorElement_def]
      have hk' : l * k⁻¹ * l⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.1 (hNW (hL.1 hl)) k⁻¹).1 (W.inv_mem (hKW hk))
      have : k * l * k⁻¹ * l⁻¹ = k * (l * k⁻¹ * l⁻¹) := by group
      rw [this]
      exact W.mul_mem (hKW hk) hk'
  have hLWc : GLAPComponent 3 W L := glaPComponent_of_le hp hL hLW hWV
  have hOW : GLAPPrimeCoreOf 3 W ≤ GLAPPrimeCoreOf 3 V := by
    have hsn : IsSubnormal W V := IsSubnormal.step hWV
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hWV).2 hNW) (IsSubnormal.refl V)
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn]
    exact inf_le_right
  have hnotW : ¬ ⁅K, L⁆ ≤ GLAPPrimeCoreOf 3 W := fun h => hK (h.trans hOW)
  obtain ⟨M, hM, hMnc⟩ : ∃ M ∈ 𝒞, ¬ ⁅L, M⁆ ≤ GLAPPrimeCoreOf 3 W := by
    by_contra hall
    push Not at hall
    have hMW_le : ∀ M ∈ 𝒞, M ≤ W := fun M hM => by
      rw [hW]; exact le_iSup₂ (f := fun M (_ : M ∈ 𝒞) => M) M hM
    have key : (⨆ M ∈ 𝒞, M) ≤ l2cZ W L := by
      refine iSup₂_le fun M hM m hm => ⟨hMW_le M hM hm, fun l hl => ?_⟩
      have h1 : ⁅l, m⁆ ∈ GLAPPrimeCoreOf 3 W :=
        hall M hM (Subgroup.commutator_mem_commutator hl hm)
      have h2 : ⁅m, l⁆ = (⁅l, m⁆)⁻¹ := by rw [commutatorElement_inv]
      rw [h2]
      exact (GLAPPrimeCoreOf 3 W).inv_mem h1
    have hZ : W ≤ l2cZ W L := hW.le.trans key
    exact hnotW (Subgroup.commutator_le.2 fun k hk l hl => (hZ (hKW hk)).2 l hl)
  have hMW' := hMW M hM
  have hLlay : L ≤ GLAPLayer 3 W := le_sSup hLWc
  have hMlay : M ≤ GLAPLayer 3 W := le_sSup hMW'
  have hLN : L ≤ Subgroup.normalizer (M : Set G) := fun l hl =>
    i183_glaPLayer_le_normalizer hp hMW' (hLlay hl)
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := fun m hm =>
    i183_glaPLayer_le_normalizer hp hLWc (hMlay hm)
  have hT : ⁅L, M⁆ ≤ L := by
    refine Subgroup.commutator_le.2 fun l hl m hm => ?_
    rw [commutatorElement_def]
    have : m * l⁻¹ * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hMN hm) l⁻¹).1 (L.inv_mem hl)
    have e : l * m * l⁻¹ * m⁻¹ = l * (m * l⁻¹ * m⁻¹) := by group
    rw [e]
    exact L.mul_mem hl this
  have hML : M ≤ L := i183_le_of_commutator hMW' hLW hLN hMN hT hMnc
  have hEq : M = L := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.glaPComponent_eq_of_le hp hMW' hLWc hML
  exact hEq ▸ hM

theorem l2c_isPGroup_zpowers {x : G} (hx3 : x ^ 3 = 1) : IsPGroup 3 ↥(Subgroup.zpowers x) := by
  have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; norm_num)

theorem l2c_zpowers_cases {x e : G} (hx3 : x ^ 3 = 1) (he : e ∈ Subgroup.zpowers x) :
    e = 1 ∨ e = x ∨ e = x * x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
  have h3 : x ^ (3 : ℤ) = 1 := by simpa using hx3
  have hk : x ^ k = x ^ (k % 3) := by
    have hkk : k = k % 3 + 3 * (k / 3) := by omega
    conv_lhs => rw [hkk]
    rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
  rw [hk]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero x)
  · exact Or.inr (Or.inl (zpow_one x))
  · exact Or.inr (Or.inr (zpow_two x))

theorem l2c_orbit (Y W : Subgroup G) (𝒞 : Set (Subgroup G)) (x : G)
    (h𝒞 : ∀ M ∈ 𝒞, GLAPComponent 3 Y M) (hW : W = ⨆ M ∈ 𝒞, M)
    (hxN : x ∈ Subgroup.normalizer (W : Set G)) (hx3 : x ^ 3 = 1)
    (K : Subgroup G) (hK : GLAPComponent 3 (W ⊓ Subgroup.centralizer ({x} : Set G)) K) :
    ∃ L ∈ 𝒞, GLAPComponent 3 (W ⊔ Subgroup.zpowers x) L ∧
      GLAPComponent 3 ((W ⊔ Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G)) K ∧
      ((GLBConj x L = L ∧ K ≤ L) ∨
        (GLBConj x L ≠ L ∧ GLBConj x (GLBConj x L) ≠ L ∧
          K ≤ L ⊔ GLBConj x L ⊔ GLBConj x (GLBConj x L))) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hEV : Subgroup.zpowers x ≤ W ⊔ Subgroup.zpowers x := le_sup_right
  have hWV : W ≤ W ⊔ Subgroup.zpowers x := le_sup_left
  have hNW : W ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (W : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hxN)
  have hWV' : (W.subgroupOf (W ⊔ Subgroup.zpowers x)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWV).2 hNW
  have hWY : W ≤ Y := by
    rw [hW]; exact iSup₂_le fun M hM => (h𝒞 M hM).1
  have hMW : ∀ M ∈ 𝒞, GLAPComponent 3 W M := fun M hM =>
    glaPComponent_of_le hp (h𝒞 M hM)
      (by rw [hW]; exact le_iSup₂ (f := fun M (_ : M ∈ 𝒞) => M) M hM) hWY
  have hMV : ∀ M ∈ 𝒞, GLAPComponent 3 (W ⊔ Subgroup.zpowers x) M := fun M hM =>
    glaPComponent_of_normal_overgroup hp hWV hWV' (hMW M hM)
  have hWlay : W ≤ GLAPLayer 3 (W ⊔ Subgroup.zpowers x) :=
    hW.le.trans (iSup₂_le fun M hM => le_sSup (hMV M hM))
  have hKV : GLAPComponent 3 ((W ⊔ Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G)) K :=
    glaPComponent_of_normal_overgroup hp (inf_le_inf_right _ hWV)
      (l2c_normal_inf hNW hWV) hK
  have hKW : K ≤ W := hK.1.trans inf_le_left
  have hKlay : K ≤ GLAPLayer 3 (W ⊔ Subgroup.zpowers x) := hKW.trans hWlay
  have hKsup : K ≤ ⨆ L ∈ i183Family 3 (W ⊔ Subgroup.zpowers x) K, L :=
    i183_le_iSup_family hp hKV hKlay
  have hEp : IsPGroup 3 ↥(Subgroup.zpowers x) := l2c_isPGroup_zpowers hx3
  have hCz : Subgroup.centralizer (Subgroup.zpowers x : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hKE : K ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [hCz]; exact hK.1.trans inf_le_right
  have hJE : GLAPComponent 3 ((W ⊔ Subgroup.zpowers x) ⊓
      Subgroup.centralizer (Subgroup.zpowers x : Set G)) K := by
    rw [hCz]; exact hKV
  have htr : ∀ L₁ ∈ i183Family 3 (W ⊔ Subgroup.zpowers x) K,
      ∀ L₂ ∈ i183Family 3 (W ⊔ Subgroup.zpowers x) K,
        ∃ e ∈ Subgroup.zpowers x, GLBConj e L₁ = L₂ :=
    fun L₁ h₁ L₂ h₂ => i183_transitive hp hEV hEp hJE hKlay h₁ h₂
  have h𝒟𝒞 : ∀ L ∈ i183Family 3 (W ⊔ Subgroup.zpowers x) K, L ∈ 𝒞 := fun L hL =>
    l2c_fam_mem hW h𝒞 hWV hNW hKW hKlay hL.1 hL.2
  have hne : ∃ L₁, L₁ ∈ i183Family 3 (W ⊔ Subgroup.zpowers x) K := by
    by_contra hemp
    have hbot : K ≤ ⊥ := hKsup.trans (iSup₂_le fun L hL => (hemp ⟨L, hL⟩).elim)
    have hq := isQuasisimple_pQuot_of_glaPComponent hp hKV
    have hK0 : K = ⊥ := le_bot_iff.1 hbot
    subst hK0
    haveI := CFSG.LocalCores.isQuasisimple_nontrivial
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq)
    have : Subsingleton (PQuot 3 (⊥ : Subgroup G)) := by unfold PQuot; infer_instance
    exact (not_subsingleton (PQuot 3 (⊥ : Subgroup G))) this
  obtain ⟨L₁, hL₁⟩ := hne
  have hL₁V : GLAPComponent 3 (W ⊔ Subgroup.zpowers x) L₁ := hL₁.1
  by_cases hfix : GLBConj x L₁ = L₁
  · refine ⟨L₁, h𝒟𝒞 L₁ hL₁, hL₁V, hKV, Or.inl ⟨hfix, ?_⟩⟩
    have hxN₁ : x ∈ Subgroup.normalizer (L₁ : Set G) :=
      mem_normalizer_iff_gLBConj_eq.2 hfix
    have hall : ∀ L ∈ i183Family 3 (W ⊔ Subgroup.zpowers x) K, L ≤ L₁ := by
      intro L hL
      obtain ⟨e, he, rfl⟩ := htr L₁ hL₁ L hL
      have hN : e ∈ Subgroup.normalizer (L₁ : Set G) := (Subgroup.zpowers_le.2 hxN₁) he
      exact (gLBConj_eq_of_mem_normalizer hN).le
    exact hKsup.trans (iSup₂_le fun L hL => hall L hL)
  · have h3ne : GLBConj x (GLBConj x L₁) ≠ L₁ := by
      intro h
      have h1 : GLBConj (x * x) L₁ = L₁ := by
        rw [← gLBConj_gLBConj]; exact h
      have hxx : x * x ∈ Subgroup.normalizer (L₁ : Set G) :=
        mem_normalizer_iff_gLBConj_eq.2 h1
      have hx4 : x * x * (x * x) = x := by
        calc x * x * (x * x) = x ^ 3 * x := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          _ = x := by rw [hx3, one_mul]
      have hxN₁ : x * x * (x * x) ∈ Subgroup.normalizer (L₁ : Set G) :=
        mul_mem hxx hxx
      rw [hx4] at hxN₁
      exact hfix (mem_normalizer_iff_gLBConj_eq.1 hxN₁)
    have hcover : ∀ L ∈ i183Family 3 (W ⊔ Subgroup.zpowers x) K,
        L ≤ L₁ ⊔ GLBConj x L₁ ⊔ GLBConj x (GLBConj x L₁) := by
      intro L hL
      obtain ⟨e, he, rfl⟩ := htr L₁ hL₁ L hL
      rcases l2c_zpowers_cases hx3 he with rfl | rfl | rfl
      · rw [gLBConj_one]; exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
      · rw [← gLBConj_gLBConj]; exact le_sup_right
    exact ⟨L₁, h𝒟𝒞 L₁ hL₁, hL₁V, hKV, Or.inr ⟨hfix, h3ne,
      hKsup.trans (iSup₂_le fun L hL => hcover L hL)⟩⟩

theorem l2c_diag {V L K : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) (hxV : x ∈ V)
    (hL : GLAPComponent 3 V L) (hKc : GLAPComponent 3 (V ⊓ Subgroup.centralizer ({x} : Set G)) K)
    (h1 : GLBConj x L ≠ L) (h2 : GLBConj x (GLBConj x L) ≠ L)
    (hKd : K ≤ L ⊔ GLBConj x L ⊔ GLBConj x (GLBConj x L)) :
    Nonempty (PSimple 3 K ≃* PSimple 3 L) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨Z, hZn, -, ⟨e⟩⟩ := i183v_diag (⟨hxV, hx3, hL, h1, h2⟩ : I183vCyc V x L) hKc hKd
  haveI := hZn
  let f : ↥L →* PQuot 3 K :=
    ((e.symm.toMonoidHom.comp (QuotientGroup.mk' Z)).comp
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective Z (e y)
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) q
    refine ⟨l, ?_⟩
    show e.symm (QuotientGroup.mk' Z (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) l)) = y
    rw [hl, hq, MulEquiv.symm_apply_apply]
  have hA := isQuasisimple_pQuot_of_glaPComponent hp hL
  have hKq := isQuasisimple_pQuot_of_glaPComponent hp hKc
  have hbot : GLAPPrimeCore 3 (PQuot 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have eB : (PQuot 3 K ⧸ GLAPPrimeCore 3 (PQuot 3 K)) ≃* PQuot 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hB : CFSG.Open.IsQuasisimple (PQuot 3 K ⧸ GLAPPrimeCore 3 (PQuot 3 K)) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eB.symm hKq
  obtain ⟨φ⟩ := nonempty_pSimple_equiv_of_surjective hp f hf hA hB
  exact ⟨(QuotientGroup.congr _ _ eB (Subgroup.map_center_eq eB)).symm.trans φ.symm⟩

end CFSG.LocalAnalysis.GLTheoremA
