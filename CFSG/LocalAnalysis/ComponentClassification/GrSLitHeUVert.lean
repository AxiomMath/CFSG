module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Std

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open CFSG.ClassicalInvolution.Balance (deltaCore)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace HeUV

theorem isKleinFour_of_card (H : Type*) [Group H] (hH : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) : IsKleinFour H := by
  refine ⟨hH, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

theorem isFourGroup_of_card {X : Type*} [Group X] {F : Subgroup X} (hF : IsElemTwo F)
    (h4 : Nat.card F = 4) : IsFourGroup F := by
  have h1 : IsKleinFour ↥F := isKleinFour_of_card ↥F h4 fun x => by
    apply Subtype.ext
    show (x : X) ^ 2 = 1
    rw [pow_two]
    exact hF.2 _ x.2
  have h2 : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    isKleinFour_of_card _ (by rw [Nat.card_prod]; simp) (by decide)
  exact IsKleinFour.nonempty_mulEquiv

theorem wGroup_eq_bot_of_le {X : Type} [Group X] [Finite X] {L E : Subgroup X}
    (hW : ∀ A : Subgroup X, A ≤ normalizer (L : Set X) → IsFourGroup A → wGroup A = ⊥)
    (hE : IsElemTwo E) (hEL : E ≤ normalizer (L : Set X)) : wGroup E = ⊥ := by
  rw [eq_bot_iff, wGroup_eq_iSup_deltaCore]
  refine iSup_le fun B => iSup_le fun hB => iSup_le fun h4 => iSup_le fun _ => ?_
  obtain ⟨F, hFB, hF4⟩ := exists_le_card_four ((hE.mono hB).isPGroup) h4
  have hFe : IsElemTwo F := hE.mono (hFB.trans hB)
  have h := hW F ((hFB.trans hB).trans hEL) (isFourGroup_of_card hFe hF4)
  calc deltaCore B ≤ deltaCore F := deltaCore_anti hFB
    _ ≤ wGroup F := by
      rw [wGroup_eq_iSup_deltaCore]
      exact le_iSup_of_le F (le_iSup_of_le le_rfl (le_iSup_of_le (by rw [hF4])
        (le_iSup_of_le (fun b hb => hFe.2 b hb) le_rfl)))
    _ = ⊥ := h

theorem cover_of_sup_eq {X : Type*} [Group X] [Finite X] {T M : Subgroup X}
    (hTM : T ≤ M) (hTO : T ⊔ (pPrimeCore 2 ↥M).map M.subtype = M) :
    Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (inclusion hTM)) ∧
      ¬ 2 ∣ Nat.card ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (inclusion hTM)).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 ↥M with hO
  set π := QuotientGroup.mk' O with hπ
  set f : ↥T →* ↥M ⧸ O := π.comp (inclusion hTM) with hf
  have htop : T.subgroupOf M ⊔ O = ⊤ := by
    have h1 : (O.map M.subtype).subgroupOf M = O :=
      comap_map_eq_self_of_injective M.subtype_injective O
    rw [← h1, ← subgroupOf_sup hTM (map_subtype_le _), hTO, subgroupOf_self]
  have hmapT : (T.subgroupOf M).map π = ⊤ := by
    have h1 : (T.subgroupOf M ⊔ O).map π = ⊤ := by
      rw [htop]
      exact map_top_of_surjective π (QuotientGroup.mk'_surjective O)
    rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff O).mpr (by rw [hπ, QuotientGroup.ker_mk']),
      sup_bot_eq] at h1
  refine ⟨fun q => ?_, ?_⟩
  · have hq : q ∈ (T.subgroupOf M).map π := by rw [hmapT]; exact mem_top q
    obtain ⟨m, hm, rfl⟩ := hq
    exact ⟨⟨m, hm⟩, rfl⟩
  · let g : f.ker →* O := ((inclusion hTM).comp f.ker.subtype).codRestrict O fun k =>
      (QuotientGroup.eq_one_iff _).mp k.2
    have hg : Function.Injective g := fun k₁ k₂ h => by
      have h' := congrArg (fun x : O => ((x : ↥M) : X)) h
      exact Subtype.ext (Subtype.ext h')
    have hodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat (Subgroup.card_dvd_of_injective g hg)) ∘
      even_iff_two_dvd.mpr

theorem mem_fusionZStar_of_sup_eq {X : Type*} [Group X] [Finite X] {T M : Subgroup X}
    (hTM : T ≤ M) (hTO : T ⊔ (pPrimeCore 2 ↥M).map M.subtype = M) {x : X}
    (hx : x ∈ (Open.fusionZStar ↥T).map T.subtype) :
    x ∈ (Open.fusionZStar ↥M).map M.subtype := by
  obtain ⟨hfs, hfk⟩ := cover_of_sup_eq hTM hTO
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  have hπk : ¬ 2 ∣ Nat.card π.ker := GSThmB.OddQuot.not_two_dvd_card_ker
  have h1 := GSThmB.OddQuot.comap_fusionZStar_of_surjective _ hfs hfk
  have h2 := GSThmB.OddQuot.comap_fusionZStar_of_surjective π (QuotientGroup.mk'_surjective _)
    hπk
  obtain ⟨t, ht, rfl⟩ := hx
  have ht' : ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (inclusion hTM)) t ∈
      Open.fusionZStar (↥M ⧸ pPrimeCore 2 ↥M) := by
    rw [← h1] at ht
    exact ht
  refine ⟨inclusion hTM t, ?_, rfl⟩
  rw [← h2]
  exact ht'

theorem conj_mem_of_normalizer {X : Type} [Group X] {M : Subgroup X} {g x : X}
    (hg : g ∈ normalizer (M : Set X)) (hx : x ∈ (pPrimeCore 2 ↥M).map M.subtype) :
    g * x * g⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype := by
  have h := GrS5.normalizer_le_normalizer_oddIn M hg
  exact (mem_normalizer_iff.mp h x).mp hx

def coreCentralizer {X : Type} [Group X] (M : Subgroup X) : Subgroup X where
  carrier := {e | e ∈ normalizer (M : Set X) ∧
    ∀ m ∈ M, e * m * e⁻¹ * m⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype}
  one_mem' := ⟨one_mem _, fun m _ => by simp⟩
  mul_mem' := by
    rintro e₁ e₂ ⟨h₁, c₁⟩ ⟨h₂, c₂⟩
    refine ⟨mul_mem h₁ h₂, fun m hm => ?_⟩
    have h := mul_mem (conj_mem_of_normalizer h₁ (c₂ m hm)) (c₁ m hm)
    rwa [show e₁ * (e₂ * m * e₂⁻¹ * m⁻¹) * e₁⁻¹ * (e₁ * m * e₁⁻¹ * m⁻¹) =
      e₁ * e₂ * m * (e₁ * e₂)⁻¹ * m⁻¹ by group] at h
  inv_mem' := by
    rintro e ⟨he, c⟩
    refine ⟨inv_mem he, fun m hm => ?_⟩
    have hm' : e⁻¹ * m * e ∈ M := by
      have := (mem_normalizer_iff.mp (inv_mem he) m).mp hm
      rwa [inv_inv] at this
    have h := inv_mem (c _ hm')
    rwa [show (e * (e⁻¹ * m * e) * e⁻¹ * (e⁻¹ * m * e)⁻¹)⁻¹ = e⁻¹ * m * e⁻¹⁻¹ * m⁻¹ by group]
      at h

def coreFixed {X : Type} [Group X] (M : Subgroup X) (g : X) : Subgroup X where
  carrier := {m | m ∈ M ∧ g * m * g⁻¹ * m⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro m₁ m₂ ⟨h₁, c₁⟩ ⟨h₂, c₂⟩
    refine ⟨mul_mem h₁ h₂, ?_⟩
    have h := mul_mem c₁ (conj_mem_of_normalizer (le_normalizer h₁) c₂)
    rwa [show g * m₁ * g⁻¹ * m₁⁻¹ * (m₁ * (g * m₂ * g⁻¹ * m₂⁻¹) * m₁⁻¹) =
      g * (m₁ * m₂) * g⁻¹ * (m₁ * m₂)⁻¹ by group] at h
  inv_mem' := by
    rintro m ⟨hm, c⟩
    refine ⟨inv_mem hm, ?_⟩
    have h := conj_mem_of_normalizer (le_normalizer (inv_mem hm)) (inv_mem c)
    rwa [show m⁻¹ * (g * m * g⁻¹ * m⁻¹)⁻¹ * m⁻¹⁻¹ = g * m⁻¹ * g⁻¹ * m⁻¹⁻¹ by group] at h

theorem central_of_invariant (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    {X : Type} [Group X] [Finite X] (hK : Assembly.KProper Blueprint.Catalog X)
    (hZ : ∀ e : X, e ≠ 1 → centralizer ({e} : Set X) ≠ ⊤)
    {L V T M : Subgroup X} {a u : X} (ha : orderOf a = 2)
    (hLa : L ≤ centralizer ({a} : Set X)) (haL : a ∉ L)
    (hW : ∀ A : Subgroup X, A ≤ normalizer (L : Set X) → IsFourGroup A → wGroup A = ⊥)
    (hVL : V ≤ L) (hV : IsElemTwo V) (hV4 : 4 ≤ Nat.card V) (huV : u ∈ V) (hu : orderOf u = 2)
    (hTa : T ≤ centralizer ({a} : Set X)) (hVT : V ≤ (Open.fusionZStar ↥T).map T.subtype)
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hMa : conjugate M a = M) (hTM : T ≤ M)
    (hTO : T ⊔ (pPrimeCore 2 ↥M).map M.subtype = M) :
    (∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) ∧
      ∀ v ∈ V, ∀ m ∈ M, v * m = m * v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  set E := V ⊔ zpowers a with hE
  have hVa : ∀ v ∈ V, v * a = a * v := fun v hv =>
    mem_centralizer_singleton_iff.mp (hLa (hVL hv))
  have hEe : IsElemTwo E := hV.sup (isElemTwo_zpowers haa) (fun x hx y hy => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute x a from hVa x hx) i).eq)
  have hE8 : 8 ≤ Nat.card E := by
    have hVE : V ≤ E := le_sup_left
    have hne : V.subgroupOf E ≠ ⊤ := by
      intro h
      have hmem : (⟨a, mem_sup_right (mem_zpowers a)⟩ : E) ∈ V.subgroupOf E := h ▸ mem_top _
      exact haL (hVL hmem)
    have hidx : 2 ≤ (V.subgroupOf E).index := by
      have h1 : (V.subgroupOf E).index ≠ 1 := fun h => hne (index_eq_one.mp h)
      have h0 : (V.subgroupOf E).index ≠ 0 := index_ne_zero_of_finite
      omega
    have hcard := card_mul_index (V.subgroupOf E)
    rw [Nat.card_congr (subgroupOfEquivOfLe hVE).toEquiv] at hcard
    calc 8 = 4 * 2 := by norm_num
      _ ≤ Nat.card V * (V.subgroupOf E).index := Nat.mul_le_mul hV4 hidx
      _ = Nat.card E := hcard
  have hEu : E ≤ centralizer ({u} : Set X) := sup_le
    (fun v hv => mem_centralizer_singleton_iff.mpr (hV.1 v hv u huV))
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hVa u huV).symm))
  have hVM : V ≤ M := fun v hv => by
    obtain ⟨t, -, rfl⟩ := hVT hv
    exact hTM t.2
  have hVZ : ∀ v ∈ V, v ∈ (Open.fusionZStar ↥M).map M.subtype := fun v hv =>
    mem_fusionZStar_of_sup_eq hTM hTO (hVT hv)
  have haN : a ∈ normalizer (M : Set X) := by
    rw [mem_normalizer_iff]
    intro y
    rw [← UnbalancedLayer.mem_conjugate_iff, hMa]
  have hEN : E ≤ normalizer (M : Set X) :=
    sup_le (hVM.trans le_normalizer) (zpowers_le.mpr haN)
  have haC : ∀ m ∈ M, a * m * a⁻¹ * m⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype := by
    have hle : T ⊔ (pPrimeCore 2 ↥M).map M.subtype ≤ coreFixed M a := by
      refine sup_le (fun t ht => ⟨hTM ht, ?_⟩) (fun o ho => ⟨map_subtype_le _ ho, ?_⟩)
      · rw [show a * t * a⁻¹ * t⁻¹ = 1 by
          rw [(mem_centralizer_singleton_iff.mp (hTa ht)).symm]; group]
        exact one_mem _
      · exact mul_mem (conj_mem_of_normalizer haN ho) (inv_mem ho)
    exact fun m hm => (hle (by rw [hTO]; exact hm)).2
  have hEC : E ≤ coreCentralizer M := by
    refine sup_le (fun v hv => ⟨le_normalizer (hVM hv), fun m hm => ?_⟩)
      (zpowers_le.mpr ⟨haN, haC⟩)
    obtain ⟨z, hz, hzv⟩ := hVZ v hv
    have h := GSThmB.OddQuot.mem_fusionZStar_iff.mp hz ⟨m, hm⟩
    refine ⟨_, h, ?_⟩
    rw [← hzv]
    simp [commutatorElement_def]
  have haNL : a ∈ normalizer (L : Set X) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [show a * y * a⁻¹ = y by rw [← mem_centralizer_singleton_iff.mp (hLa hy)]; group]
      exact hy
    · intro hy
      have h := mem_centralizer_singleton_iff.mp (hLa hy)
      have h' : y = a * y * a⁻¹ := by
        calc y = a⁻¹ * ((a * y * a⁻¹) * a) := by group
          _ = a⁻¹ * (a * (a * y * a⁻¹)) := by rw [h]
          _ = a * y * a⁻¹ := by group
      rw [h']
      exact hy
  have hWE : wGroup E = ⊥ :=
    wGroup_eq_bot_of_le hW hEe (sup_le (hVL.trans le_normalizer) (zpowers_le.mpr haNL))
  have hbal : ∀ e ∈ E, e ≠ 1 →
      ⁅(pPrimeCore 2 ↥M).map M.subtype ⊓ centralizer ({e} : Set X),
        (pLayer ↥(M ⊓ centralizer ({e} : Set X)) 2).map
          (M ⊓ centralizer ({e} : Set X)).subtype⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype :=
    fun e he he1 => GrS5.commutator_oddCore_pLayer_le hS hU hheld hK hu hMu hMp
      (mem_centralizer_singleton_iff.mp (hEu he)).symm (hZ e he1)
  have hc := oddCore_le_center_of_wGroup_eq_bot hMu hMp hEu hEe.1 hEe.2 (by omega) hEN
    (fun e he => (hEC he).2) hWE hbal (Or.inr hE8)
  refine ⟨hc, fun v hv m hm => ?_⟩
  have hperf : Group.IsPerfect ↥M := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hMp
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hMu).toMonoidHom)
      (subgroupOfEquivOfLe hMu).surjective
  have hO : pPrimeCore 2 ↥M ≤ center ↥M := fun x hx =>
    mem_center_iff.mpr fun g => Subtype.ext (hc _ ⟨x, hx, rfl⟩ _ g.2).symm
  have hZM := GrS5.fusionZStar_eq_center_of_le hperf.commutator_eq_top hO
  obtain ⟨z, hz, hzv⟩ := hVZ v hv
  rw [hZM] at hz
  have h := mem_center_iff.mp hz ⟨m, hm⟩
  rw [← hzv]
  exact (congrArg Subtype.val h).symm

end HeUV

end CFSG.ComponentClassification.GrSLit
