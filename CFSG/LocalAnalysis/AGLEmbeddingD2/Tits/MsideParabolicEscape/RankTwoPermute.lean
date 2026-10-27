module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.EscapeCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NonConstrainedStructure

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open scoped Pointwise

@[expose] def innSub (N : Type) [Group N] : Subgroup (MulAut N) :=
  (MulAut.conj : N →* MulAut N).range

@[expose] def KFactRankTwoSylowPermute : Prop :=
  ∀ (N : Type) [Group N] [Finite N], IsSimpleGroup N → ¬ IsMulCommutative N →
    IsRankTwoLayerType N → ∀ Y : Subgroup (MulAut N), innSub N ≤ Y →
      (innSub N).relIndex Y ≤ 2 →
      (Nonempty (N ≃* alternatingGroup (Fin 6)) → (innSub N).relIndex Y = 2 →
        Nonempty (↥Y ≃* Equiv.Perm (Fin 6))) →
      (StatedClassicalModel N .PSL 3 2 1 → (innSub N).relIndex Y = 1) →
      ∀ S : Subgroup (MulAut N), IsSylowTwoOf S Y →
        ∃ P : Subgroup (MulAut N), P ≤ innSub N ∧ Nat.card P = 3 ∧
          (S : Set (MulAut N)) * P = (P : Set (MulAut N)) * S

theorem center_eq_bot_of_simple {N : Type} [Group N] (hs : IsSimpleGroup N)
    (hnc : ¬ IsMulCommutative N) : Subgroup.center N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with h | h
  · exact h
  · exfalso
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have hb : b ∈ Subgroup.center N := by rw [h]; trivial
    exact Subgroup.mem_center_iff.mp hb a

theorem conj_injective_of_simple {N : Type} [Group N] (hs : IsSimpleGroup N)
    (hnc : ¬ IsMulCommutative N) : Function.Injective (MulAut.conj : N →* MulAut N) := by
  intro a b hab
  have hc := center_eq_bot_of_simple hs hnc
  have hz : b⁻¹ * a ∈ Subgroup.center N := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h : a * x * a⁻¹ = b * x * b⁻¹ := by
      have := congrArg (fun f : MulAut N => f x) hab
      simpa [MulAut.conj_apply] using this
    have h' : a * x = b * x * b⁻¹ * a := by
      calc a * x = (a * x * a⁻¹) * a := by group
        _ = (b * x * b⁻¹) * a := by rw [h]
    calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹ * a) := by group
      _ = b⁻¹ * (a * x) := by rw [h']
      _ = (b⁻¹ * a) * x := by group
  rw [hc, Subgroup.mem_bot] at hz
  exact (inv_mul_eq_one.mp hz).symm

section Transport

variable {X : Type} [Group X] [Finite X]

@[expose] def autImage (N : Subgroup X) [N.Normal] : Subgroup (MulAut ↥N) :=
  (MulAut.conjNormal : X →* MulAut ↥N).range

@[expose] def AutImageOK (N : Subgroup X) [N.Normal] : Prop :=
  (innSub ↥N).relIndex (autImage N) ≤ 2 ∧
    (Nonempty (↥N ≃* alternatingGroup (Fin 6)) → (innSub ↥N).relIndex (autImage N) = 2 →
      Nonempty (↥(autImage N) ≃* Equiv.Perm (Fin 6))) ∧
    (StatedClassicalModel ↥N .PSL 3 2 1 → (innSub ↥N).relIndex (autImage N) = 1)

omit [Finite X] in
theorem conjNormal_coe_eq {N : Subgroup X} [N.Normal] (n : ↥N) :
    (MulAut.conjNormal (H := N) (n : X)) = MulAut.conj n := by
  ext m
  simp [MulAut.conjNormal_apply, MulAut.conj_apply]

theorem isSylowTwoOf_sup_of_inf {N V : Subgroup X} [N.Normal] (hV2 : IsPGroup 2 V)
    (hVN : IsSylowTwoOf (V ⊓ N) N) : IsSylowTwoOf V (V ⊔ N) := by
  refine ⟨le_sup_left, hV2, ?_⟩
  have hcs := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_normal V N
  have hr := Subgroup.relIndex_mul_card (H := V) (K := V ⊔ N)
  rw [inf_of_le_left (le_sup_left : V ≤ V ⊔ N)] at hr
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have key : V.relIndex (V ⊔ N) * Nat.card (V ⊓ N : Subgroup X) = Nat.card N := by
    have h : Nat.card V * (V.relIndex (V ⊔ N) * Nat.card (V ⊓ N : Subgroup X)) =
        Nat.card V * Nat.card N := by
      rw [← hcs, ← hr]
      ring
    exact Nat.eq_of_mul_eq_mul_left hVpos h
  have h2 := Subgroup.relIndex_mul_card (H := V ⊓ N) (K := N)
  rw [inf_of_le_left (inf_le_right : V ⊓ N ≤ N)] at h2
  have h3 : V.relIndex (V ⊔ N) = (V ⊓ N).relIndex N := by
    have hpos : 0 < Nat.card (V ⊓ N : Subgroup X) := Nat.card_pos
    have : V.relIndex (V ⊔ N) * Nat.card (V ⊓ N : Subgroup X) =
        (V ⊓ N).relIndex N * Nat.card (V ⊓ N : Subgroup X) := by
      rw [key, ← h2]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  show ¬ 2 ∣ V.relIndex (V ⊔ N)
  rw [h3]
  exact hVN.2.2

theorem exists_permuting_of_kfact (hK : KFactRankTwoSylowPermute) {N V : Subgroup X} [N.Normal]
    (hs : IsSimpleGroup ↥N) (hnc : ¬ IsMulCommutative ↥N) (hty : IsRankTwoLayerType ↥N)
    (hV2 : IsPGroup 2 V) (hVN : IsSylowTwoOf (V ⊓ N) N) (hok : AutImageOK N) :
    ∃ P : Subgroup X, P ≤ N ∧ Nat.card P = 3 ∧ (P : Set X) * V = (V : Set X) * P := by
  set φ : X →* MulAut ↥N := MulAut.conjNormal with hφ
  have hinj := conj_injective_of_simple hs hnc
  set Λ : Subgroup X := V ⊔ N with hΛ
  set Y : Subgroup (MulAut ↥N) := Λ.map φ with hY
  have hInnY : innSub ↥N ≤ Y := by
    rintro _ ⟨n, rfl⟩
    exact ⟨(n : X), (le_sup_right : N ≤ V ⊔ N) n.2, conjNormal_coe_eq n⟩
  have hYx : Y ≤ autImage N := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hΛsyl : IsSylowTwoOf V Λ := isSylowTwoOf_sup_of_inf hV2 hVN
  have hVsyl : IsSylowTwoOf (V.map φ) Y := by
    have h := isSylowTwoOf_map_range (φ.comp Λ.subtype) hΛsyl
    have e1 : (V.subgroupOf Λ).map (φ.comp Λ.subtype) = V.map φ := by
      rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left le_sup_left]
    have e2 : (φ.comp Λ.subtype).range = Y := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rwa [e1, e2] at h
  have : Finite (MulAut ↥N) :=
    Finite.of_injective (fun f : MulAut ↥N => (f : ↥N → ↥N)) DFunLike.coe_injective
  have hfin : (innSub ↥N).relIndex (autImage N) ≠ 0 := by
    intro h
    have := Subgroup.relIndex_mul_card (H := innSub ↥N) (K := autImage N)
    rw [h, zero_mul] at this
    exact (Nat.card_pos (α := ↥(autImage N))).ne' this.symm
  have hidxY : (innSub ↥N).relIndex Y ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hYx hfin).trans hok.1
  have hmul : (innSub ↥N).relIndex Y * Y.relIndex (autImage N) = (innSub ↥N).relIndex (autImage N) :=
    Subgroup.relIndex_mul_relIndex _ _ _ hInnY hYx
  have hA6Y : Nonempty (↥N ≃* alternatingGroup (Fin 6)) → (innSub ↥N).relIndex Y = 2 →
      Nonempty (↥Y ≃* Equiv.Perm (Fin 6)) := by
    intro ha h2
    have hrx : (innSub ↥N).relIndex (autImage N) = 2 := by
      have := Subgroup.relIndex_le_of_le_right hYx hfin
      have := hok.1
      omega
    rw [h2, hrx] at hmul
    have h1 : Y.relIndex (autImage N) = 1 := by omega
    have hYeq : Y = autImage N :=
      le_antisymm hYx (Subgroup.relIndex_eq_one.mp h1)
    obtain ⟨e⟩ := hok.2.1 ha hrx
    exact ⟨(MulEquiv.subgroupCongr hYeq).trans e⟩
  have hL32Y : StatedClassicalModel ↥N .PSL 3 2 1 → (innSub ↥N).relIndex Y = 1 := by
    intro h
    have hrx := hok.2.2 h
    rw [hrx] at hmul
    exact Nat.eq_one_of_mul_eq_one_right hmul
  obtain ⟨Pb, hPbInn, hPb3, hperm⟩ :=
    hK ↥N hs hnc hty Y hInnY hidxY hA6Y hL32Y (V.map φ) hVsyl
  set f : ↥N →* MulAut ↥N := MulAut.conj with hf
  have hfrange : f.range = innSub ↥N := rfl
  set Pn : Subgroup ↥N := Pb.comap f with hPn
  set P : Subgroup X := Pn.map N.subtype with hP
  have hPN : P ≤ N := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hPcard : Nat.card P = 3 := by
    rw [hP, Subgroup.card_map_of_injective N.subtype_injective]
    have h1 : Pn.map f = Pb := by
      rw [hPn, Subgroup.map_comap_eq, hfrange, inf_of_le_right hPbInn]
    rw [← hPb3, ← h1, Subgroup.card_map_of_injective hinj]
  refine ⟨P, hPN, hPcard, ?_⟩
  have hkey : ∀ v ∈ V, ∀ p ∈ P, ∃ n ∈ V ⊓ N, ∃ p' ∈ P, v * p * v⁻¹ = n * p' := by
    intro v hv p hp
    obtain ⟨pn, hpn, rfl⟩ := hp
    have hpPb : f pn ∈ Pb := hpn
    have hmem : f pn * (φ v)⁻¹ ∈ (Pb : Set (MulAut ↥N)) * ((V.map φ : Subgroup _) : Set _) :=
      Set.mem_mul.mpr ⟨f pn, hpPb, (φ v)⁻¹, (V.map φ).inv_mem ⟨v, hv, rfl⟩, rfl⟩
    rw [← hperm] at hmem
    obtain ⟨a, ha, q, hq, haq⟩ := Set.mem_mul.mp hmem
    obtain ⟨v₃, hv₃, rfl⟩ := ha
    set n' : ↥N := (φ v) pn with hn'
    have hnat : φ v * f pn * (φ v)⁻¹ = f n' := by
      ext m
      simp [hf, hn', MulAut.conj_apply]
    have hy : f n' = φ (v * v₃) * q := by
      rw [← hnat, map_mul]
      calc φ v * f pn * (φ v)⁻¹ = φ v * (f pn * (φ v)⁻¹) := by group
        _ = φ v * (φ v₃ * q) := by rw [← haq]
        _ = φ v * φ v₃ * q := by group
    obtain ⟨p₁, hp₁⟩ := hPbInn hq
    have hp₁Pn : p₁ ∈ Pn := by
      show f p₁ ∈ Pb
      rw [hp₁]
      exact hq
    have hin : φ (v * v₃) ∈ innSub ↥N := by
      have : φ (v * v₃) = f n' * q⁻¹ := by rw [hy]; group
      rw [this]
      exact Subgroup.mul_mem _ ⟨n', rfl⟩ (Subgroup.inv_mem _ (hPbInn hq))
    obtain ⟨n₁, hn₁⟩ := hin
    have hnn : n' = n₁ * p₁ := by
      apply hinj
      rw [map_mul]
      show f n' = f n₁ * f p₁
      rw [hy, ← hn₁, hp₁]
    have hn₁V : (n₁ : X) ∈ V ⊓ N := by
      set SV : Subgroup ↥N := (V.map φ).comap f with hSV
      have hn₁SV : n₁ ∈ SV := by
        show f n₁ ∈ V.map φ
        rw [hn₁]
        exact ⟨v * v₃, V.mul_mem hv hv₃, rfl⟩
      have hSV2 : IsPGroup 2 SV := (hV2.map φ).comap_of_injective f hinj
      have hSX2 : IsPGroup 2 (SV.map N.subtype) := hSV2.map N.subtype
      have hSle : V ⊓ N ≤ SV.map N.subtype := by
        intro x hx
        refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
        show f ⟨x, hx.2⟩ ∈ V.map φ
        exact ⟨x, hx.1, (conjNormal_coe_eq (N := N) ⟨x, hx.2⟩)⟩
      have hSXN : SV.map N.subtype ≤ N := by
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      have heq := hVN.eq_of_le hSle hSXN hSX2
      rw [← heq]
      exact ⟨n₁, hn₁SV, rfl⟩
    refine ⟨(n₁ : X), hn₁V, (p₁ : X), ⟨p₁, hp₁Pn, rfl⟩, ?_⟩
    have h2 : (((φ v) pn : ↥N) : X) = v * (pn : X) * v⁻¹ := MulAut.conjNormal_apply v pn
    exact h2.symm.trans (congrArg Subtype.val hnn)
  have hsub : ∀ p ∈ P, ∀ v ∈ V, p * v ∈ (V : Set X) * (P : Set X) := by
    intro p hp v hv
    obtain ⟨n, hn, p', hp', he⟩ := hkey v⁻¹ (V.inv_mem hv) p hp
    refine Set.mem_mul.mpr ⟨v * n, V.mul_mem hv hn.1, p', hp', ?_⟩
    calc v * n * p' = v * (n * p') := by group
      _ = v * (v⁻¹ * p * v⁻¹⁻¹) := by rw [he]
      _ = p * v := by group
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, v, hv, rfl⟩ := Set.mem_mul.mp hx
    exact hsub p hp v hv
  · intro hx
    obtain ⟨v, hv, p, hp, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨v', hv', p', hp', he⟩ := Set.mem_mul.mp (hsub p⁻¹ (P.inv_mem hp) v⁻¹ (V.inv_mem hv))
    refine Set.mem_mul.mpr ⟨p'⁻¹, P.inv_mem hp', v'⁻¹, V.inv_mem hv', ?_⟩
    calc p'⁻¹ * v'⁻¹ = (v' * p')⁻¹ := by group
      _ = (p⁻¹ * v⁻¹)⁻¹ := by rw [he]
      _ = v * p := by group

end Transport

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
