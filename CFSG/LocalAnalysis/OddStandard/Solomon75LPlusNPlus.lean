module

public import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusFunctor

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

variable {A B X : Type} [Group A] [Group B] [Group X]

@[expose] def NPlus (X : Type) [Group X] : Subgroup X :=
  (NOne (X ⧸ pPrimeCore 2 X) ⊔ NTwo (X ⧸ pPrimeCore 2 X)).comap
    (QuotientGroup.mk' (pPrimeCore 2 X))

theorem pPrimeCore_le_NPlus : pPrimeCore 2 X ≤ NPlus X := by
  intro x hx
  have h : QuotientGroup.mk' (pPrimeCore 2 X) x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
  show QuotientGroup.mk' (pPrimeCore 2 X) x ∈
    (NOne (X ⧸ pPrimeCore 2 X) ⊔ NTwo (X ⧸ pPrimeCore 2 X))
  rw [h]
  exact one_mem _

theorem NPlus_comap [Finite A] (φ : A →* B) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ pPrimeCore 2 A) : (NPlus B).comap φ = NPlus A := by
  let e := quotEquivOfKer φ hφ hker
  have hcomp : (QuotientGroup.mk' (pPrimeCore 2 B)).comp φ =
      e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 A)) := by
    ext a
    rfl
  have himg : NOne (B ⧸ pPrimeCore 2 B) ⊔ NTwo (B ⧸ pPrimeCore 2 B) =
      (NOne (A ⧸ pPrimeCore 2 A) ⊔ NTwo (A ⧸ pPrimeCore 2 A)).map e.toMonoidHom := by
    rw [Subgroup.map_sup, NOne_map, NTwo_map]
  unfold NPlus
  rw [Subgroup.comap_comap, hcomp, ← Subgroup.comap_comap, himg,
    Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective]

theorem NPlus_eq_of_pPrimeCore_eq_bot [Finite B] (h : pPrimeCore 2 B = ⊥) :
    NPlus B = NOne B ⊔ NTwo B := by
  have hinj : Function.Injective (QuotientGroup.mk' (pPrimeCore 2 B)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', h]
  let e : B ≃* (B ⧸ pPrimeCore 2 B) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (pPrimeCore 2 B))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have himg : NOne (B ⧸ pPrimeCore 2 B) ⊔ NTwo (B ⧸ pPrimeCore 2 B) =
      (NOne B ⊔ NTwo B).map e.toMonoidHom := by
    rw [Subgroup.map_sup, NOne_map, NTwo_map]
  unfold NPlus
  change (NOne (B ⧸ pPrimeCore 2 B) ⊔ NTwo (B ⧸ pPrimeCore 2 B)).comap e.toMonoidHom = _
  rw [himg, Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective]

theorem NPlus_map_equiv [Finite A] (e : A ≃* B) : (NPlus A).map e.toMonoidHom = NPlus B := by
  have h := NPlus_comap e.toMonoidHom e.surjective (by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : x = 1 := e.injective (by simpa using hx)
    rw [this]
    exact one_mem _)
  rw [← h]
  exact Subgroup.map_comap_eq_self_of_surjective e.surjective _

theorem NPlus_map_aut [Finite A] (φ : MulAut A) : (NPlus A).map φ.toMonoidHom = NPlus A :=
  NPlus_map_equiv φ

theorem normal_of_map_aut (H : Subgroup X) (h : ∀ φ : MulAut X, H.map φ.toMonoidHom = H) :
    H.Normal := by
  refine ⟨fun x hx g => ?_⟩
  have : MulAut.conj g x ∈ H.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rw [h] at this
  simpa using this

instance EPlus_normal : (EPlus X).Normal := normal_of_map_aut _ EPlus_map_aut

instance NPlus_normal : (NPlus X).Normal := by
  unfold NPlus
  have h1 : (NOne (X ⧸ pPrimeCore 2 X)).Normal := NOne_normal
  have h2 : (NTwo (X ⧸ pPrimeCore 2 X)).Normal := NTwo_normal
  exact Subgroup.Normal.comap (Subgroup.sup_normal _ _) _

instance LPlus_normal : (LPlus X).Normal := by
  unfold LPlus
  exact Subgroup.Normal.comap inferInstance _

theorem LPlus_eq_pLayer_sup_NPlus [Finite X] : LPlus X = pLayer X 2 ⊔ NPlus X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := QuotientGroup.mk' (pPrimeCore 2 X) with hq
  have hs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have h1 : (layer (X ⧸ pPrimeCore 2 X)).comap q = pLayer X 2 ⊔ pPrimeCore 2 X :=
    ComponentClassification.LBalance.Quot.comap_layer_quotient_eq (H := X) (p := 2)
  have h2 := Subgroup.comap_sup_eq (f := q) (layer (X ⧸ pPrimeCore 2 X))
    (NOne (X ⧸ pPrimeCore 2 X) ⊔ NTwo (X ⧸ pPrimeCore 2 X)) hs
  have hO : pPrimeCore 2 X ≤ (NOne (X ⧸ pPrimeCore 2 X) ⊔ NTwo (X ⧸ pPrimeCore 2 X)).comap q :=
    pPrimeCore_le_NPlus
  unfold LPlus NPlus EPlus
  rw [sup_assoc, ← h2, h1, sup_assoc, sup_eq_right.mpr hO]

theorem IsCommProd.subgroupOf {Q : Type} [Group Q] {W : Type} [Group W] {N : Subgroup W}
    (h : IsCommProd Q N) (K : Subgroup W) (hNK : N ≤ K) : IsCommProd Q (N.subgroupOf K) := by
  classical
  obtain ⟨S, hS, hc, hsup⟩ := h
  have hFK : ∀ F ∈ S, F ≤ K := fun F hF => (le_sup_of_mem hF).trans (hsup ▸ hNK)
  refine ⟨S.image (fun F : Subgroup W => F.subgroupOf K), ?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hF
    exact ⟨(Subgroup.subgroupOfEquivOfLe (hFK A hA)).trans (hS A hA).some⟩
  · intro F hF F' hF' hne
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hF)
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hF')
    have hAA' : A ≠ A' := fun h => hne (by rw [h])
    have h1 := hc (Finset.mem_coe.mpr hA) (Finset.mem_coe.mpr hA') hAA'
    refine (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (hFK A hA),
      Subgroup.map_subgroupOf_eq_of_le (hFK A' hA')]
    exact h1
  · have h1 : ((S.image (fun F : Subgroup W => F.subgroupOf K)).sup id).map K.subtype = N := by
      rw [map_finset_sup, Finset.image_image, Finset.sup_image, ← hsup]
      refine Finset.sup_congr rfl fun F hF => ?_
      simp only [Function.comp, id]
      exact Subgroup.map_subgroupOf_eq_of_le (hFK F hF)
    exact Subgroup.map_injective K.subtype_injective
      (h1.trans (Subgroup.map_subgroupOf_eq_of_le hNK).symm)

section Lemma25N

theorem map_subtype_normal_of_map_aut (B : Subgroup X) [B.Normal] (N : Subgroup ↥B)
    (h : ∀ φ : MulAut ↥B, N.map φ.toMonoidHom = N) : (N.map B.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hx
  have hmem : (MulAut.conjNormal g : MulAut B) y ∈ N := by
    have : (MulAut.conjNormal g : MulAut B) y ∈ N.map (MulAut.conjNormal g).toMonoidHom :=
      ⟨y, hy, rfl⟩
    rwa [h] at this
  exact ⟨_, hmem, by simp⟩

theorem NOne_le_of_normal [Finite X] (B : Subgroup X) [B.Normal] (h3 : pCore 3 B = ⊥) :
    (NOne B).map B.subtype ≤ NOne X := by
  obtain ⟨-, hNc, -⟩ := lemma_2_4_one h3
  exact le_NOne (map_subtype_normal_of_map_aut B _ NOne_map_aut)
    (hNc.map_hom B.subtype B.subtype_injective)

theorem NTwo_le_of_normal [Finite X] (B : Subgroup X) [B.Normal] (h3 : pCore 3 B = ⊥) :
    (NTwo B).map B.subtype ≤ NTwo X := by
  obtain ⟨-, hNc, -⟩ := lemma_2_4_two h3
  exact le_NTwo (map_subtype_normal_of_map_aut B _ NTwo_map_aut)
    (hNc.map_hom B.subtype B.subtype_injective)

theorem nPlus_le_of_normal [Finite X] (Y : Subgroup X) [Y.Normal] :
    (NPlus ↥Y).map Y.subtype ≤ NPlus X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := QuotientGroup.mk' (pPrimeCore 2 X) with hq
  set Yb : Subgroup (X ⧸ pPrimeCore 2 X) := Y.map q with hYb
  have hYbn : Yb.Normal := Subgroup.Normal.map ‹Y.Normal› q (QuotientGroup.mk'_surjective _)
  let φ : ↥Y →* ↥Yb := (q.comp Y.subtype).codRestrict Yb (fun y => ⟨y, y.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : φ.ker ≤ pPrimeCore 2 ↥Y := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hyq : q (y : X) = 1 := congrArg Subtype.val hy
    have hyO : (y : X) ∈ pPrimeCore 2 X := (QuotientGroup.eq_one_iff _).mp hyq
    set D : Subgroup ↥Y := (pPrimeCore 2 X).subgroupOf Y with hD
    have hDn : D.Normal := Subgroup.normal_subgroupOf
    have hDcop : Nat.Coprime 2 (Nat.card D) := by
      have hle : D.map Y.subtype ≤ pPrimeCore 2 X := by
        rintro _ ⟨d, hd, rfl⟩
        exact hd
      have hdvd : Nat.card D ∣ Nat.card (pPrimeCore 2 X) := by
        have hcard : Nat.card (D.map Y.subtype) = Nat.card D :=
          Subgroup.card_map_of_injective Y.subtype_injective
        rw [← hcard]
        exact Subgroup.card_dvd_of_le hle
      exact Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card
    exact (le_sSup ⟨hDn, hDcop⟩ : D ≤ pPrimeCore 2 ↥Y) hyO
  have hcomap := NPlus_comap φ hφs hker
  have hO : pPrimeCore 2 ↥Yb = ⊥ :=
    pPrimeCore_eq_bot_of_normal (pPrimeCore_quotient_pPrimeCore_eq_bot 2) Yb
  have hLE : NPlus ↥Yb = NOne ↥Yb ⊔ NTwo ↥Yb := NPlus_eq_of_pPrimeCore_eq_bot hO
  have h3 := pCore_three_eq_bot hO
  have hE : (NOne ↥Yb ⊔ NTwo ↥Yb).map Yb.subtype ≤
      NOne (X ⧸ pPrimeCore 2 X) ⊔ NTwo (X ⧸ pPrimeCore 2 X) := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (NOne_le_of_normal Yb h3) (NTwo_le_of_normal Yb h3)
  rintro _ ⟨y, hy, rfl⟩
  have hy' : φ y ∈ NPlus ↥Yb := by
    have : y ∈ (NPlus ↥Yb).comap φ := hcomap ▸ hy
    exact this
  rw [hLE] at hy'
  exact hE ⟨φ y, hy', rfl⟩

end Lemma25N

section Ambient

variable {G : Type} [Group G]

@[expose] def LPlusIn (H : Subgroup G) : Subgroup G := (LPlus ↥H).map H.subtype

@[expose] def NPlusIn (H : Subgroup G) : Subgroup G := (NPlus ↥H).map H.subtype

theorem LPlusIn_le (H : Subgroup G) : LPlusIn H ≤ H := Subgroup.map_subtype_le _

theorem LPlusIn_le_of_normal [Finite G] {D C : Subgroup G} (hDC : D ≤ C)
    (hn : C ≤ normalizer (D : Set G)) : LPlusIn D ≤ LPlusIn C := by
  have hnorm : (D.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDC).mpr hn
  have h := lPlus_le_of_normal (D.subgroupOf C)
  let e := Subgroup.subgroupOfEquivOfLe hDC
  have hmap : (LPlus ↥(D.subgroupOf C)).map e.toMonoidHom = LPlus ↥D := LPlus_map_equiv e
  have hcomp : D.subtype.comp e.toMonoidHom = C.subtype.comp (D.subgroupOf C).subtype := by
    ext x
    rfl
  unfold LPlusIn
  rw [← hmap, Subgroup.map_map, hcomp, ← Subgroup.map_map]
  exact Subgroup.map_mono h

theorem NPlusIn_le_of_normal [Finite G] {D C : Subgroup G} (hDC : D ≤ C)
    (hn : C ≤ normalizer (D : Set G)) : NPlusIn D ≤ NPlusIn C := by
  have hnorm : (D.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDC).mpr hn
  have h := nPlus_le_of_normal (D.subgroupOf C)
  let e := Subgroup.subgroupOfEquivOfLe hDC
  have hmap : (NPlus ↥(D.subgroupOf C)).map e.toMonoidHom = NPlus ↥D := NPlus_map_equiv e
  have hcomp : D.subtype.comp e.toMonoidHom = C.subtype.comp (D.subgroupOf C).subtype := by
    ext x
    rfl
  unfold NPlusIn
  rw [← hmap, Subgroup.map_map, hcomp, ← Subgroup.map_map]
  exact Subgroup.map_mono h

theorem normalizer_le_normalizer_map_subtype (Y : Subgroup G) (P : Subgroup ↥Y)
    (hP : ∀ φ : MulAut ↥Y, P.map φ.toMonoidHom = P) :
    normalizer (Y : Set G) ≤ normalizer ((P.map Y.subtype : Subgroup G) : Set G) := by
  have fwd : ∀ g ∈ normalizer (Y : Set G), ∀ z ∈ P.map Y.subtype,
      g * z * g⁻¹ ∈ P.map Y.subtype := by
    intro g hg z hz
    obtain ⟨y, hy, rfl⟩ := hz
    let c := Subgroup.normalizerMonoidHom Y ⟨g, hg⟩
    have hcy : (c y : G) = g * (y : G) * g⁻¹ := rfl
    have hmem : c y ∈ P := by
      have : c y ∈ P.map c.toMonoidHom := ⟨y, hy, rfl⟩
      rwa [hP c] at this
    exact ⟨c y, hmem, hcy⟩
  intro g hg
  rw [mem_normalizer_iff]
  intro z
  refine ⟨fwd g hg z, fun h => ?_⟩
  have := fwd g⁻¹ ((normalizer (Y : Set G)).inv_mem hg) _ h
  have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
  rwa [e] at this

end Ambient

end CFSG.OddStandard.Solomon75
