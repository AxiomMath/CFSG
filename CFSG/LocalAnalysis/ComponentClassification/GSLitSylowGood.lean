module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitIsoTarget

public section

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {G : Type*} [Group G]

theorem conjugate_le_normalizer {X Y : Subgroup G} (h : X ≤ normalizer (Y : Set G)) (g : G) :
    conjugate X g ≤ normalizer (conjugate Y g : Set G) := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  apply mem_normalizer_of_conjugate_eq
  have hgx : g * x = (g * x * g⁻¹) * g := by group
  rw [conjugate_conjugate, hgx, ← conjugate_conjugate, conjugate_eq_of_mem_normalizer (h hx)]

theorem card_conjugate (X : Subgroup G) (g : G) : Nat.card (conjugate X g) = Nat.card X :=
  card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjugate_map_pPrimeCore (K : Subgroup G) (g : G) :
    conjugate ((pPrimeCore 2 K).map K.subtype) g =
      (pPrimeCore 2 (conjugate K g)).map (conjugate K g).subtype :=
  map_map_pPrimeCore (MulAut.conj g⁻¹) K

theorem conjugate_centralizer (F : Subgroup G) (g : G) :
    conjugate (centralizer (F : Set G)) g = centralizer (conjugate F g : Set G) :=
  map_centralizer_subgroup (MulAut.conj g⁻¹) F

theorem isPComponent_conjugate_centralizer {F K : Subgroup G}
    (hKF : K ≤ centralizer (F : Set G))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer (F : Set G)))) (g : G) :
    conjugate K g ≤ centralizer (conjugate F g : Set G) ∧
      IsPComponent 2 ((conjugate K g).subgroupOf (centralizer (conjugate F g : Set G))) := by
  set φ : G ≃* G := MulAut.conj g⁻¹ with hφ
  have hC : (centralizer (F : Set G)).map φ.toMonoidHom = centralizer (conjugate F g : Set G) :=
    conjugate_centralizer F g
  refine ⟨hC ▸ map_mono hKF, ?_⟩
  let ψ : centralizer (F : Set G) ≃* centralizer (conjugate F g : Set G) :=
    ((centralizer (F : Set G)).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hC)
  have h := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 ψ hK
  convert h using 1
  ext y
  constructor
  · intro hy
    obtain ⟨j, hj, hjy⟩ := mem_map.mp (mem_subgroupOf.mp hy)
    exact ⟨⟨j, hKF hj⟩, mem_subgroupOf.mpr hj, Subtype.ext hjy⟩
  · rintro ⟨w, hw, rfl⟩
    exact mem_subgroupOf.mpr ⟨w, mem_subgroupOf.mp hw, rfl⟩

theorem conjugate_sup_pPrimeCore {A K : Subgroup G}
    (h : A ⊔ (pPrimeCore 2 K).map K.subtype = K) (g : G) :
    conjugate A g ⊔ (pPrimeCore 2 (conjugate K g)).map (conjugate K g).subtype =
      conjugate K g := by
  rw [← conjugate_map_pPrimeCore]
  unfold conjugate
  rw [← Subgroup.map_sup, h]

theorem mem_normalizer_centralizer {S : Subgroup G} {g : G} (hg : g ∈ normalizer (S : Set G)) :
    g ∈ normalizer (centralizer (S : Set G) : Set G) := by
  apply mem_normalizer_of_conjugate_eq
  have h1 := conjugate_centralizer S g
  rw [conjugate_eq_of_mem_normalizer hg] at h1
  exact h1

variable [Finite G]

theorem exists_mem_normalizer_not_mem {H U : Subgroup G} (hU : IsPGroup 2 U) (hHU : H < U) :
    ∃ u ∈ U, u ∉ H ∧ u ∈ normalizer (H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent U := hU.isNilpotent
  have hlt : H.subgroupOf U < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hHU.ne
    apply le_antisymm hHU.le
    intro x hx
    have h1 : (⟨x, hx⟩ : U) ∈ H.subgroupOf U := htop ▸ mem_top _
    exact mem_subgroupOf.mp h1
  obtain ⟨u, hu, hnot⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  exact ⟨u, u.2, fun h => hnot (mem_subgroupOf.mpr h),
    mem_normalizer_of_subgroupOf hHU.le hu⟩

omit [Finite G] in
theorem exists_lt_of_not_sylow {Q Y : Subgroup G} (hQY : Q ≤ Y) (hQ : IsPGroup 2 Q)
    (hnot : ¬ ∃ P₀ : Sylow 2 ↥Y, (P₀ : Subgroup Y) = Q.subgroupOf Y) :
    ∃ U : Subgroup G, U ≤ Y ∧ IsPGroup 2 U ∧ Q < U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := (hQ.comap_subtype (K := Y)).exists_le_sylow
  refine ⟨(P₀ : Subgroup Y).map Y.subtype, map_subtype_le _, P₀.isPGroup'.map _,
    lt_of_le_of_ne ?_ ?_⟩
  · intro x hx
    exact ⟨⟨x, hQY hx⟩, hP₀ (show (⟨x, hQY hx⟩ : Y) ∈ Q.subgroupOf Y from hx), rfl⟩
  · intro heq
    apply hnot
    refine ⟨P₀, ?_⟩
    rw [heq, subgroupOf, comap_map_eq_self_of_injective Y.subtype_injective]

namespace B2Setting

variable {a : G} {J S : Subgroup G}

omit [Finite G] in
theorem conjugate_ne_bot {F : Subgroup G} (hF : F ≠ ⊥) (g : G) : conjugate F g ≠ ⊥ := by
  intro h
  apply hF
  rw [← conjugate_conjugate_inv F g, h]
  unfold conjugate
  exact Subgroup.map_bot _

theorem le_normalizer_cover (h : B2Setting a J S) {F K : Subgroup G}
    (hF : F ≤ S ⊓ coreActionKernel J) (hne : F ≠ ⊥) (hK : IsCover J F K) :
    S ⊓ normalizer (F : Set G) ≤ normalizer (F : Set G) ⊓ normalizer (K : Set G) := fun _s hs =>
  mem_inf.mpr ⟨(mem_inf.mp hs).2,
    (h.mem_coreActionKernel_cover_iff hF hne hK (mem_inf.mp hs).1 (mem_inf.mp hs).2).1⟩

omit [Finite G] in
theorem le_normalizer_P (h : B2Setting a J S) :
    S ≤ normalizer ((S ⊓ coreActionKernel J : Subgroup G) : Set G) := fun _s hs =>
  normalizer_inf_mem (le_normalizer hs)
    (normalizer_le_normalizer_coreActionKernel J (mem_inf.mp (h.le_H hs)).2)

end B2Setting

@[expose] def SylowGood (S F K : Subgroup G) : Prop :=
  ∃ P₀ : Sylow 2 ↥(normalizer (F : Set G) ⊓ normalizer (K : Set G)),
    (P₀ : Subgroup _) = (S ⊓ normalizer (F : Set G)).subgroupOf
      (normalizer (F : Set G) ⊓ normalizer (K : Set G))

namespace B2Setting

variable {a : G} {J S : Subgroup G}

theorem not_lt_of_eq_P (h : B2Setting a J S) {F K Q₁ : Subgroup G}
    (hFP : F = S ⊓ coreActionKernel J) (hK : IsCover J F K) (hQ₁2 : IsPGroup 2 Q₁)
    (hQQ₁ : S ⊓ normalizer (F : Set G) < Q₁)
    (hQ₁N : Q₁ ≤ normalizer ((S ⊓ normalizer (F : Set G) : Subgroup G) : Set G))
    (hQ₁Y : Q₁ ≤ normalizer (F : Set G) ⊓ normalizer (K : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hFP
  set P := S ⊓ coreActionKernel J with hPdef
  have hQS : S ⊓ normalizer (P : Set G) = S :=
    le_antisymm inf_le_left (le_inf le_rfl h.le_normalizer_P)
  rw [hQS] at hQQ₁ hQ₁N
  have ha1 : a ≠ 1 := by
    intro ha
    have h1 := h.orderOf_eq
    rw [ha, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  set Z₀ := P ⊓ centralizer (S : Set G) with hZ₀
  have haZ : a ∈ Z₀ := mem_inf.mpr ⟨mem_inf.mpr ⟨h.a_mem, h.a_mem_coreActionKernel⟩,
    mem_centralizer_iff.mpr fun s hs => h.comm_a s hs⟩
  have hZne : Z₀ ≠ ⊥ := fun hb => ha1 (by rw [hb, mem_bot] at haZ; exact haZ)
  have hZQ₁ : Z₀ ≤ Q₁ := (inf_le_left.trans inf_le_left).trans hQQ₁.le
  have hQ₁Z : Q₁ ≤ normalizer (Z₀ : Set G) := fun q hq =>
    normalizer_inf_mem (hQ₁Y hq).1 (mem_normalizer_centralizer (hQ₁N hq))
  obtain ⟨b, hbZ, hb, hbc⟩ := exists_involution_mem_center hQ₁2 hZQ₁ hQ₁Z hZne
  have hbP : b ∈ P := (mem_inf.mp hbZ).1
  have hbS : b ∈ S := (mem_inf.mp hbP).1
  have hbcS : ∀ s ∈ S, s * b = b * s := fun s hs => mem_centralizer_iff.mp (mem_inf.mp hbZ).2 s hs
  obtain ⟨L, hL⟩ := h.exists_isoTarget hb hbP
  obtain ⟨-, Pb, hPb⟩ :=
    h.central b L hb (h.mem_H_of_mem hbP).1 (h.mem_H_of_mem hbP).2 hL hbS hbcS
  have hPb' : P ≤ centralizer ({b} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hbcS x (mem_inf.mp hx).1)
  obtain ⟨hPL, hcov⟩ := h.isCover_fixedLayer le_rfl hbP hPb' hL
  have hKeq : K = fixedLayer L P := hK.unique hcov
  obtain ⟨hC, -, -⟩ := gsIsoCorr_iff_sup.mp hL
  have hLb := hC.2.2.2.2.2.1
  have hLp := hC.2.2.2.2.2.2.1
  obtain ⟨-, -, hLq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hLb).1 hLp
  have hP2 : IsPGroup 2 P := h.isPGroup.to_le inf_le_left
  have hcover : K ⊔ (pPrimeCore 2 L).map L.subtype = L := by
    have h1 := (fixedLayer_nested hLq hPL hP2 (zpowers_le.mpr hbP)).2
    rw [fixedLayer_zpowers, gsFixedLayer_eq_self hLb hLp] at h1
    rw [hKeq]
    exact h1
  have hQ₁H : Q₁ ≤ centralizer ({b} : Set G) ⊓ normalizer (L : Set G) := by
    intro q hq
    have hqb : q * b = b * q := hbc q hq
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hqb, ?_⟩
    apply mem_normalizer_of_conjugate_eq
    have hφb : (MulAut.conj q⁻¹) b = b := by
      rw [MulAut.conj_apply, inv_inv]
      calc q⁻¹ * b * q = q⁻¹ * (b * q) := by group
        _ = q⁻¹ * (q * b) := by rw [hqb]
        _ = b := by group
    obtain ⟨hLq1, hLq2⟩ := isPComponent_map_centralizer (MulAut.conj q⁻¹) hLb hLp
    rw [hφb] at hLq1 hLq2
    have hcov' := conjugate_sup_pPrimeCore hcover q
    rw [conjugate_eq_of_mem_normalizer (hQ₁Y hq).2] at hcov'
    exact eq_of_isPComponent_cover hLq1 hLq2 hLb hLp hcov' hcover
  have hle : (Pb : Subgroup _) ≤
      Q₁.subgroupOf (centralizer ({b} : Set G) ⊓ normalizer (L : Set G)) := by
    rw [hPb]
    exact fun x hx => mem_subgroupOf.mpr (hQQ₁.le (mem_subgroupOf.mp hx))
  have heq := Pb.is_maximal' (Q := Q₁.subgroupOf _) hQ₁2.comap_subtype hle
  have hQ₁le : Q₁ ≤ S := fun q hq => by
    have h1 : (⟨q, hQ₁H hq⟩ : ↥(centralizer ({b} : Set G) ⊓ normalizer (L : Set G))) ∈
        Q₁.subgroupOf (centralizer ({b} : Set G) ⊓ normalizer (L : Set G)) := hq
    rw [heq, hPb] at h1
    exact mem_subgroupOf.mp h1
  exact hQQ₁.ne (le_antisymm hQQ₁.le hQ₁le)

end B2Setting

namespace B2Setting

variable {a : G} {J S : Subgroup G}

theorem exists_conjugate_of_lt_P (h : B2Setting a J S) {F KF Q₁ : Subgroup G}
    (hF : F ≤ S ⊓ coreActionKernel J) (hFP : F ≠ S ⊓ coreActionKernel J) (hne : F ≠ ⊥)
    (hKF : IsCover J F KF) (hQ₁2 : IsPGroup 2 Q₁)
    (hQ₁Q : Q₁ ≤ normalizer ((S ⊓ normalizer (F : Set G) : Subgroup G) : Set G))
    (hQ₁F : Q₁ ≤ normalizer (F : Set G)) (hQ₁K : Q₁ ≤ normalizer (KF : Set G))
    (ih : ∀ T KT : Subgroup G, T ≤ S ⊓ coreActionKernel J → T ≠ ⊥ → Nat.card F < Nat.card T →
      IsCover J T KT → ∃ y : G, conjugate T y ≤ S ⊓ coreActionKernel J ∧
        IsCover J (conjugate T y) (conjugate KT y) ∧ SylowGood S (conjugate T y) (conjugate KT y)) :
    ∃ g : G, conjugate F g ≤ S ⊓ coreActionKernel J ∧ IsCover J (conjugate F g) (conjugate KF g) ∧
      Nat.card Q₁ ≤ Nat.card ↥(S ⊓ normalizer (conjugate F g : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥(S ⊓ coreActionKernel J) := h.isPGroup.to_le inf_le_left
  set T := (S ⊓ normalizer (F : Set G)) ⊓ coreActionKernel KF with hTdef
  have hTP : T ≤ S ⊓ coreActionKernel J := fun t ht => by
    obtain ⟨htQ, htK⟩ := mem_inf.mp ht
    obtain ⟨htS, htF⟩ := mem_inf.mp htQ
    exact mem_inf.mpr ⟨htS, ((h.mem_coreActionKernel_cover_iff hF hne hKF htS htF).2).mpr htK⟩
  have hFT : F ≤ T := fun f hf => mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp (hF hf)).1,
    le_normalizer hf⟩, mem_coreActionKernel_of_le_centralizer
      (hKF.1.trans (centralizer_le (Set.singleton_subset_iff.mpr hf)))⟩
  obtain ⟨p, hpP, hpF, hpN⟩ := exists_mem_normalizer_not_mem hP2 (lt_of_le_of_ne hF hFP)
  have hpT : p ∈ T := mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hpP).1, hpN⟩,
    ((h.mem_coreActionKernel_cover_iff hF hne hKF (mem_inf.mp hpP).1 hpN).2).mp
      (mem_inf.mp hpP).2⟩
  have hFT' : F < T := lt_of_le_of_ne hFT fun heq => hpF (heq ▸ hpT)
  have hTF : T ≤ normalizer (F : Set G) := inf_le_left.trans inf_le_right
  obtain ⟨-, hcovT, hcovKF⟩ := h.isCover_nested hFT hTP hTF hne hKF
  have hTne : T ≠ ⊥ := fun hb => hne (le_bot_iff.mp (hb ▸ hFT))
  obtain ⟨y, hyP, hyK, P₀, hP₀⟩ :=
    ih T (fixedLayer KF T) hTP hTne (Subgroup.card_lt_of_lt hFT') hcovT
  have hQ₁T : Q₁ ≤ normalizer (T : Set G) := fun q hq =>
    normalizer_inf_mem (hQ₁Q hq) (normalizer_le_normalizer_coreActionKernel KF (hQ₁K hq))
  have hQ₁KT : Q₁ ≤ normalizer (fixedLayer KF T : Set G) := fun q hq =>
    mem_normalizer_fixedLayer (hQ₁K hq) (hQ₁T hq)
  have hQ₁yH : conjugate Q₁ y ≤ normalizer (conjugate T y : Set G) ⊓
      normalizer (conjugate (fixedLayer KF T) y : Set G) :=
    le_inf (conjugate_le_normalizer hQ₁T y) (conjugate_le_normalizer hQ₁KT y)
  have hQ₁y2 : IsPGroup 2 (conjugate Q₁ y) := hQ₁2.map _
  obtain ⟨w, hwH, hw⟩ := exists_conjugate_le_of_sylow ⟨P₀, hP₀⟩ hQ₁yH hQ₁y2
  have hwT : conjugate (conjugate T y) w = conjugate T y :=
    conjugate_eq_of_mem_normalizer (mem_inf.mp hwH).1
  have hwKT : conjugate (conjugate (fixedLayer KF T) y) w = conjugate (fixedLayer KF T) y :=
    conjugate_eq_of_mem_normalizer (mem_inf.mp hwH).2
  set F' := conjugate (conjugate F y) w with hF'
  have hF'T : F' ≤ conjugate T y := by
    rw [hF', ← hwT]
    exact map_mono (map_mono hFT)
  have hF'P : F' ≤ S ⊓ coreActionKernel J := hF'T.trans hyP
  have hF'ne : F' ≠ ⊥ := conjugate_ne_bot (conjugate_ne_bot hne y) w
  have hT'F' : conjugate T y ≤ normalizer (F' : Set G) := by
    have h1 := conjugate_le_normalizer (conjugate_le_normalizer hTF y) w
    rwa [hwT] at h1
  obtain ⟨K', hK'⟩ := h.exists_isCover hF'P hF'ne
  obtain ⟨-, hcovT', hcovK'⟩ := h.isCover_nested hF'T hyP hT'F' hF'ne hK'
  have hKTeq : fixedLayer K' (conjugate T y) = conjugate (fixedLayer KF T) y :=
    hcovT'.unique hyK
  rw [hKTeq] at hcovK'
  obtain ⟨hKF1, hKF2⟩ := isPComponent_conjugate_centralizer hKF.1 hKF.2.1 y
  obtain ⟨hKF1', hKF2'⟩ := isPComponent_conjugate_centralizer hKF1 hKF2 w
  have hcovKF'' := conjugate_sup_pPrimeCore (conjugate_sup_pPrimeCore hcovKF y) w
  rw [hwKT] at hcovKF''
  have hKeq := eq_of_isPComponent_cover hK'.1 hK'.2.1 hKF1' hKF2' hcovK' hcovKF''
  refine ⟨y * w, ?_, ?_, ?_⟩
  · rw [← conjugate_conjugate]
    exact hF'P
  · rw [← conjugate_conjugate, ← conjugate_conjugate, ← hKeq]
    exact hK'
  · rw [← conjugate_conjugate]
    have hle : conjugate (conjugate Q₁ y) w ≤ S ⊓ normalizer (F' : Set G) :=
      le_inf (hw.trans inf_le_left)
        (conjugate_le_normalizer (conjugate_le_normalizer hQ₁F y) w)
    calc Nat.card Q₁ = Nat.card ↥(conjugate (conjugate Q₁ y) w) := by
          rw [card_conjugate, card_conjugate]
      _ ≤ Nat.card ↥(S ⊓ normalizer (F' : Set G)) := card_le_of_le hle

theorem exists_sylowGood (h : B2Setting a J S) {E K : Subgroup G}
    (hE : E ≤ S ⊓ coreActionKernel J) (hne : E ≠ ⊥) (hK : IsCover J E K) :
    ∃ g : G, conjugate E g ≤ S ⊓ coreActionKernel J ∧ IsCover J (conjugate E g) (conjugate K g) ∧
      SylowGood S (conjugate E g) (conjugate K g) := by
  classical
  suffices H : ∀ n : ℕ, ∀ E K : Subgroup G,
      Nat.card ↥(S ⊓ coreActionKernel J) - Nat.card E = n →
      E ≤ S ⊓ coreActionKernel J → E ≠ ⊥ → IsCover J E K →
      ∃ g : G, conjugate E g ≤ S ⊓ coreActionKernel J ∧
        IsCover J (conjugate E g) (conjugate K g) ∧ SylowGood S (conjugate E g) (conjugate K g) from
    H _ E K rfl hE hne hK
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E K hn hE hne hK
  let Γ := {g : G // conjugate E g ≤ S ⊓ coreActionKernel J ∧
    IsCover J (conjugate E g) (conjugate K g)}
  have : Nonempty Γ := ⟨⟨1, by rw [conjugate_one]; exact hE,
    by rw [conjugate_one, conjugate_one]; exact hK⟩⟩
  obtain ⟨⟨g, hgP, hgK⟩, hmax⟩ :=
    Finite.exists_max (fun γ : Γ => Nat.card ↥(S ⊓ normalizer (conjugate E γ.1 : Set G)))
  refine ⟨g, hgP, hgK, ?_⟩
  by_contra hnot
  have hFne := conjugate_ne_bot hne g
  have hQY := h.le_normalizer_cover hgP hFne hgK
  have hQ2 : IsPGroup 2 ↥(S ⊓ normalizer (conjugate E g : Set G)) := h.isPGroup.to_le inf_le_left
  obtain ⟨U, hUY, hU2, hQU⟩ := exists_lt_of_not_sylow hQY hQ2 hnot
  obtain ⟨u, huU, huQ, huN⟩ := exists_mem_normalizer_not_mem hU2 hQU
  have hQ₁Y : S ⊓ normalizer (conjugate E g : Set G) ⊔ zpowers u ≤
      normalizer (conjugate E g : Set G) ⊓ normalizer (conjugate K g : Set G) :=
    sup_le hQY (zpowers_le.mpr (hUY huU))
  have hQ₁2 : IsPGroup 2 ↥(S ⊓ normalizer (conjugate E g : Set G) ⊔ zpowers u) :=
    hU2.to_le (sup_le hQU.le (zpowers_le.mpr huU))
  have hQQ₁ : S ⊓ normalizer (conjugate E g : Set G) <
      S ⊓ normalizer (conjugate E g : Set G) ⊔ zpowers u :=
    lt_of_le_of_ne le_sup_left fun heq => huQ (heq ▸ mem_sup_right (mem_zpowers u))
  have hQ₁N : S ⊓ normalizer (conjugate E g : Set G) ⊔ zpowers u ≤
      normalizer ((S ⊓ normalizer (conjugate E g : Set G) : Subgroup G) : Set G) :=
    sup_le le_normalizer (zpowers_le.mpr huN)
  by_cases hFP : conjugate E g = S ⊓ coreActionKernel J
  · exact h.not_lt_of_eq_P hFP hgK hQ₁2 hQQ₁ hQ₁N hQ₁Y
  · obtain ⟨g', hg'P, hg'K, hcard⟩ := h.exists_conjugate_of_lt_P hgP hFP hFne hgK hQ₁2 hQ₁N
      (hQ₁Y.trans inf_le_left) (hQ₁Y.trans inf_le_right) fun T KT hTP hTne hlt hKT => by
        have hTle : Nat.card T ≤ Nat.card ↥(S ⊓ coreActionKernel J) := card_le_of_le hTP
        have hEg : Nat.card ↥(conjugate E g) = Nat.card E := card_conjugate E g
        exact ih _ (by omega) T KT rfl hTP hTne hKT
    have hm := hmax ⟨g * g', by rw [← conjugate_conjugate]; exact hg'P,
      by rw [← conjugate_conjugate, ← conjugate_conjugate]; exact hg'K⟩
    dsimp only at hm
    rw [← conjugate_conjugate] at hm
    have hlt := Subgroup.card_lt_of_lt hQQ₁
    omega

end B2Setting

end CFSG.ComponentClassification.GSLit
