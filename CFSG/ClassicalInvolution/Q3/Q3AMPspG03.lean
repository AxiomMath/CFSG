module

public import CFSG.ClassicalInvolution.Q3.Q3AMPspG02
public import CFSG.ClassicalInvolution.Q3.Q3Y2Comp

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Q3.Q3AM
open scoped commutatorElement MatrixGroups

section Gen



variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem BadStd8.exactLayer3_generation (hTwin : Q3Y2.ModelTwinGen3)
    (h : BadStd8 Ω K J S R T W z t) (hint : IsIntrinsicU (.sl2 3 1) K z)
    {K' : Subgroup G} (hKK' : K' ∈ omegaNbr Ω K) (hJK' : K' ∈ omegaNbr Ω J)
    {t₁ t₂ t₃ : G} {R₁ R₂ R₃ : Subgroup G}
    (hax : BadAxis K J K' z t t₁ t₂ t₃ R₁ R₂ R₃) :
    Q3NL.exactLayer3 Ω z ≤ oddCoreIn (Q3NL.exactLayer3 Ω z) ⊔
      ⨆ F ∈ signalizerFunctorEk 2 2 (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)),
        (Subgroup.centralizer (F : Set G) ⊓ Q3NL.exactLayer3 Ω z) := by
  classical
  have hs := h.std
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hnab : ∃ a b : G, a * b ≠ b * a := h.nonabelian
  have hz1 : IsUniqueInvolution K z := hs.hz
  have hz1sq : z * z = 1 := hz1.sq
  have hz2sq : t * t = 1 := hs.ht.sq
  have hz3sq : (z * t) * (z * t) = 1 := hax.uniq₃.sq
  have hzt : z * t = t * z := hax.z_comm
  have hnc : ¬ ({z} : Set G) ⊆ Subgroup.center G :=
    Q3W.not_subset_center_of_ne_one hnab hz1.ne_one
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hz1sq
  obtain ⟨ι, -, ⟨D⟩⟩ := Q3T7.lieSystemMod3_exactPair3_of_stand3 hs3 hc2 hnc
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (isUniqueInvolution_comm hz1 hu)
  have hKtq : K ∈ Q3NL.tqMembers3 Ω z := Q3NL.mem_tqMembers3_of_le_centralizer hKΩ hKz
  have hJtq : J ∈ Q3NL.tqMembers3 Ω z := mem_tqMembers3_of_omegaNbr hΩ hnt hz1 hs.hJ hs.ht
  have hK'tq : K' ∈ Q3NL.tqMembers3 Ω z := mem_tqMembers3_of_omegaNbr hΩ hnt hz1 hKK' hax.uniq₃
  have hKcl : Q3.IsClassicalMember3 K z :=
    isClassicalMember3_of_uniqueInvolution hs.stand.modU hKΩ hz1
  have hJcl : Q3.IsClassicalMember3 J t :=
    isClassicalMember3_of_uniqueInvolution hs.stand.modU hs.hJ.1 hs.ht
  have hK'cl : Q3.IsClassicalMember3 K' (z * t) :=
    isClassicalMember3_of_uniqueInvolution hs.stand.modU hKK'.1 hax.uniq₃
  have mem_core : ∀ {M : Subgroup G} {x : G}, x ∈ M → x * z = z * x →
      x ∈ Q3NL.exactCore3 z M := fun hxM hc =>
    ⟨hxM, Subgroup.mem_centralizer_singleton_iff.mpr hc⟩
  have hzK : z ∈ Q3NL.exactCore3 z K := mem_core hz1.mem rfl
  have ht₁K : t₁ ∈ Q3NL.exactCore3 z K :=
    mem_core (hax.syl₁.1 hax.mem₁) (isUniqueInvolution_comm hz1 (hax.syl₁.1 hax.mem₁))
  have htJ : t ∈ Q3NL.exactCore3 z J := mem_core hs.ht.mem hzt.symm
  have ht₂J : t₂ ∈ Q3NL.exactCore3 z J :=
    mem_core (hax.syl₂.1 hax.mem₂) (hax.comm₁₂ z hax.z_mem₁ t₂ hax.mem₂).symm
  have hztK' : z * t ∈ Q3NL.exactCore3 z K' := mem_core hax.uniq₃.mem (by
    calc (z * t) * z = z * (t * z) := by group
      _ = z * (z * t) := by rw [hzt])
  have ht₃K' : t₃ ∈ Q3NL.exactCore3 z K' :=
    mem_core (hax.syl₃.1 hax.mem₃) (hax.comm₁₃ z hax.z_mem₁ t₃ hax.mem₃).symm
  set Y : Subgroup G := Q3NL.exactLayer3 Ω z with hYdef
  have hYC : Y ≤ Subgroup.centralizer ({z} : Set G) := Q3NL.exactLayer3_le_centralizer Ω z
  have hC₁Y : Q3NL.exactCore3 z K ≤ Y := Q3NL.exactCore3_le_exactLayer3 hKtq
  have hC₂Y : Q3NL.exactCore3 z J ≤ Y := Q3NL.exactCore3_le_exactLayer3 hJtq
  have hC₃Y : Q3NL.exactCore3 z K' ≤ Y := Q3NL.exactCore3_le_exactLayer3 hK'tq
  have hzY : z ∈ Y := hC₁Y hzK
  have htY : t ∈ Y := hC₂Y htJ
  have hztY : z * t ∈ Y := hC₃Y hztK'
  have ht₁Y : t₁ ∈ Y := hC₁Y ht₁K
  have ht₂Y : t₂ ∈ Y := hC₂Y ht₂J
  have ht₃Y : t₃ ∈ Y := hC₃Y ht₃K'
  have hsY : t₁ * t₂ * t₃ ∈ Y := Y.mul_mem (Y.mul_mem ht₁Y ht₂Y) ht₃Y
  have htsY : t * (t₁ * t₂ * t₃) ∈ Y := Y.mul_mem htY hsY
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  have hmemK : ∀ {L : Subgroup G} {x : G} (hx : x ∈ Y), x ∈ L → π ⟨x, hx⟩ ∈ modOddIn Y L :=
    fun {L x} hx hxL => ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr hxL, rfl⟩
  have hmk_sq : ∀ (x : G) (hx : x ∈ Y), x * x = 1 → π ⟨x, hx⟩ * π ⟨x, hx⟩ = 1 := by
    intro x hx hx2
    rw [← map_mul]
    have : (⟨x, hx⟩ : ↥Y) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hmk_mul : ∀ (x y : G) (hx : x ∈ Y) (hy : y ∈ Y),
      π ⟨x, hx⟩ * π ⟨y, hy⟩ = π ⟨x * y, Y.mul_mem hx hy⟩ := by
    intro x y hx hy
    rw [← map_mul]
    rfl
  have hζ₁c : ∀ x : ↥Y ⧸ classicalInvolutionOddCore ↥Y,
      π ⟨z, hzY⟩ * x = x * π ⟨z, hzY⟩ := by
    intro x
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hYC x'.2)).symm
  have hζ₁sq := hmk_sq z hzY hz1sq
  have hζ₂sq := hmk_sq t htY hz2sq
  have hζ₁ : π ⟨z, hzY⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution Y hzY hz1sq hz1.ne_one
  have hζ₂ : π ⟨t, htY⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution Y htY hz2sq hs.ht.ne_one
  have hz₃π : π ⟨z, hzY⟩ * π ⟨t, htY⟩ = π ⟨z * t, hztY⟩ := hmk_mul z t hzY htY
  have hζ₃ : π ⟨z, hzY⟩ * π ⟨t, htY⟩ ≠ 1 := by
    rw [hz₃π]
    exact Q3Y.mk_ne_one_of_involution Y hztY hz3sq hax.uniq₃.ne_one
  have hne : modOddIn Y (Q3NL.exactCore3 z J) ≠ modOddIn Y (Q3NL.exactCore3 z K') := by
    intro hEq
    obtain ⟨hzt1, hC₂cl⟩ := Q3NL.isClassicalMember3In_exactCore3 hJcl hc2 hJtq.2 hC₂Y hYC
    obtain ⟨hzt2, hC₃cl⟩ := Q3NL.isClassicalMember3In_exactCore3 hK'cl hc2 hK'tq.2 hC₃Y hYC
    have h1 := hC₂cl.map_oddQuotient
    have h2 := hC₃cl.map_oddQuotient
    unfold modOddIn at hEq
    rw [← hEq] at h2
    have h3 := Q3.involution_unique3 h1 h2
    have h4 : π ⟨t, htY⟩ = π ⟨z, hzY⟩ * π ⟨t, htY⟩ := by
      rw [hmk_mul]
      exact h3
    exact hζ₁ (mul_right_cancel (h4.symm.trans (one_mul _).symm))
  have hK₂₃ : ∀ a ∈ modOddIn Y (Q3NL.exactCore3 z J), ∀ b ∈ modOddIn Y (Q3NL.exactCore3 z K'),
      a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have haC : (a : G) ∈ Q3NL.exactCore3 z J := Subgroup.mem_subgroupOf.mp ha
    have hbC : (b : G) ∈ Q3NL.exactCore3 z K' := Subgroup.mem_subgroupOf.mp hb
    have hc := h.commMod_exactCore3 hint hKK' hJK' hax.uniq₃ rfl (a : G) haC (b : G) hbC
    exact (mk_comm_eq_iff a.2 b.2).mpr hc
  set A : Subgroup G := Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G) with hAdef
  have hs2 : (t₁ * t₂ * t₃) * (t₁ * t₂ * t₃) = 1 := hax.s_mul_self
  have hcz : z * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * z := hax.s_comm₁.eq
  have hct : t * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * t := hax.s_comm₂.eq
  have hspair : t₁ * t₂ * t₃ ∉ Subgroup.closure ({z, t} : Set G) := hax.s_not_mem_pair
  have hAA : IsElemAbelian 2 A := T8T.isElemAbelian_closure_three hz1sq hz2sq hs2 hzt hcz hct
  have hzA : z ∈ A := Subgroup.subset_closure (by simp)
  have htA : t ∈ A := Subgroup.subset_closure (by simp)
  have hsA : t₁ * t₂ * t₃ ∈ A := Subgroup.subset_closure (by simp)
  have hzpair : z ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have htpair : t ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have hs1 : t₁ * t₂ * t₃ ≠ 1 := fun e => hspair (e ▸ Subgroup.one_mem _)
  have hsz : t₁ * t₂ * t₃ ≠ z := fun e => hspair (e ▸ hzpair)
  have hts1 : t * (t₁ * t₂ * t₃) ≠ 1 := by
    intro e
    apply hspair
    have : t₁ * t₂ * t₃ = t := by
      calc t₁ * t₂ * t₃ = (t * t) * (t₁ * t₂ * t₃) := by rw [hz2sq, one_mul]
        _ = t * (t * (t₁ * t₂ * t₃)) := by group
        _ = t := by rw [e, mul_one]
    rw [this]
    exact htpair
  have htsz : t * (t₁ * t₂ * t₃) ≠ z := by
    intro e
    apply hspair
    have : t₁ * t₂ * t₃ = t * z := by
      calc t₁ * t₂ * t₃ = (t * t) * (t₁ * t₂ * t₃) := by rw [hz2sq, one_mul]
        _ = t * (t * (t₁ * t₂ * t₃)) := by group
        _ = t * z := by rw [e]
    rw [this]
    exact Subgroup.mul_mem _ htpair hzpair
  have hts2 : (t * (t₁ * t₂ * t₃)) * (t * (t₁ * t₂ * t₃)) = 1 := by
    calc (t * (t₁ * t₂ * t₃)) * (t * (t₁ * t₂ * t₃))
        = t * ((t₁ * t₂ * t₃) * t) * (t₁ * t₂ * t₃) := by group
      _ = t * (t * (t₁ * t₂ * t₃)) * (t₁ * t₂ * t₃) := by rw [← hct]
      _ = (t * t) * ((t₁ * t₂ * t₃) * (t₁ * t₂ * t₃)) := by group
      _ = 1 := by rw [hz2sq, hs2, one_mul]
  have htsA : t * (t₁ * t₂ * t₃) ∈ A := A.mul_mem htA hsA
  set H₀ : Subgroup G := ⨆ F ∈ signalizerFunctorEk 2 2 A,
    (Subgroup.centralizer (F : Set G) ⊓ Y) with hH₀
  show Y ≤ oddCoreIn Y ⊔ H₀
  set P : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y) := (H₀.subgroupOf Y).map π with hP
  have hlift : ∀ (f : G) (hfA : f ∈ A) (hfY : f ∈ Y), f ≠ 1 → f ≠ z → f * f = 1 →
      ∀ q, π ⟨f, hfY⟩ * q = q * π ⟨f, hfY⟩ → q ∈ P := by
    intro f hfA hfY hf1 hfz hf2 q hq
    obtain ⟨y, hyf, hyq⟩ := Q3Y2.centralizer_mk_le Y hfY hf2 hq
    have hcomm : z * f = f * z :=
      congrArg Subtype.val (hAA.1.is_comm.comm (⟨z, hzA⟩ : A) ⟨f, hfA⟩)
    have hF4 := Balance.Bootstrap.card_closure_pair_eq_four hz1sq hf2 hz1.ne_one hf1 hfz.symm hcomm
    have hFA : Subgroup.closure ({z, f} : Set G) ≤ A := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      exacts [hzA, hfA]
    have hF : Subgroup.closure ({z, f} : Set G) ∈ signalizerFunctorEk 2 2 A :=
      ⟨hFA, by rw [hF4]; norm_num⟩
    have hyz : (y : G) * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp (hYC y.2)
    have hyF : (y : G) ∈ Subgroup.centralizer (Subgroup.closure ({z, f} : Set G) : Set G) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro x hx
      rcases hx with rfl | hx
      · exact hyz.symm
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hyf.symm
    have hyJ : (y : G) ∈ H₀ :=
      (le_iSup₂ (f := fun (F : Subgroup G) (_ : F ∈ signalizerFunctorEk 2 2 A) =>
        Subgroup.centralizer (F : Set G) ⊓ Y) _ hF) ⟨hyF, y.2⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mpr hyJ, hyq⟩
  have hsπ : π ⟨t₁, ht₁Y⟩ * π ⟨t₂, ht₂Y⟩ * π ⟨t₃, ht₃Y⟩ = π ⟨t₁ * t₂ * t₃, hsY⟩ := by
    rw [hmk_mul, hmk_mul]
  have htsπ : π ⟨t, htY⟩ * π ⟨t₁ * t₂ * t₃, hsY⟩ = π ⟨t * (t₁ * t₂ * t₃), htsY⟩ :=
    hmk_mul _ _ htY hsY
  have hθ₂ : π ⟨t₂, ht₂Y⟩ * π ⟨t₂, ht₂Y⟩ = π ⟨t, htY⟩ := by
    rw [hmk_mul]
    congr 1
    exact Subtype.ext hax.sq₂
  have hθ₃ : π ⟨t₃, ht₃Y⟩ * π ⟨t₃, ht₃Y⟩ = π ⟨z, hzY⟩ * π ⟨t, htY⟩ := by
    rw [hmk_mul, hz₃π]
    congr 1
    exact Subtype.ext hax.sq₃
  have hθ₁ζ : π ⟨t, htY⟩ * π ⟨t₁, ht₁Y⟩ = π ⟨t₁, ht₁Y⟩ * π ⟨t, htY⟩ := by
    rw [hmk_mul, hmk_mul]
    congr 1
    exact (Subtype.ext (hax.comm₁₂ t₁ hax.mem₁ t hax.z_mem₂)).symm
  have hζ₃K : π ⟨z, hzY⟩ * π ⟨t, htY⟩ ∈ modOddIn Y (Q3NL.exactCore3 z K') := by
    rw [hz₃π]
    exact hmemK hztY hztK'
  have hrange : ∀ i : ι, (D.hom i).range ≤ P := by
    intro i
    by_cases hi : ∀ q ∈ (D.hom i).range, π ⟨t, htY⟩ * q = q * π ⟨t, htY⟩
    · intro q hq
      exact hlift t htA htY hs.ht.ne_one (Ne.symm hax.ne) hz2sq q (hi q hq)
    · have hcomp := Q3Y2.component_le_of_not_centralized D hTwin (Layer.layerImg3_mem hKtq)
        (Layer.layerImg3_mem hJtq) (Layer.layerImg3_mem hK'tq) hne hK₂₃ hζ₁c hζ₁sq hζ₁ hζ₂
        hζ₂sq hζ₃ (hmemK hzY hzK) (hmemK htY htJ) hζ₃K (hmemK ht₁Y ht₁K) (hmemK ht₂Y ht₂J)
        (hmemK ht₃Y ht₃K') hθ₂ hθ₃ hθ₁ζ i hi
      refine hcomp.trans (sup_le (sup_le ?_ ?_) ?_)
      · intro q hq
        exact hlift t htA htY hs.ht.ne_one (Ne.symm hax.ne) hz2sq q
          (Subgroup.mem_centralizer_singleton_iff.mp hq).symm
      · intro q hq
        rw [hsπ] at hq
        exact hlift (t₁ * t₂ * t₃) hsA hsY hs1 hsz hs2 q
          (Subgroup.mem_centralizer_singleton_iff.mp hq).symm
      · intro q hq
        rw [hsπ, htsπ] at hq
        exact hlift (t * (t₁ * t₂ * t₃)) htsA htsY hts1 htsz hts2 q
          (Subgroup.mem_centralizer_singleton_iff.mp hq).symm
  have htop : (⊤ : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y)) ≤ P := by
    rw [← D.generate]
    exact iSup_le hrange
  refine Q3Y2.oddCoreIn_sup_of_range_le Y fun y => ?_
  obtain ⟨j, hjJ, hjy⟩ := (show π y ∈ P from htop trivial)
  exact ⟨j, Subgroup.mem_subgroupOf.mp hjJ, hjy⟩

end Gen

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
