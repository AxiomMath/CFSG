module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Main213
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Orbit
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Diag
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Solv
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Cent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open scoped Pointwise

section Lift

variable {H : Type*} [Group H] [Finite H] {p : ℕ}

theorem noSimpleSec_centralizer_of_quotient (hp : p.Prime) (O : Subgroup H) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {z : H} (hz : IsPGroup p (zpowers z))
    (h : NoSimpleSec p ↥(centralizer ({QuotientGroup.mk' O z} : Set (H ⧸ O)))) :
    NoSimpleSec p ↥(centralizer ({z} : Set H)) := by
  set π := QuotientGroup.mk' O with hπ
  have hmem : ∀ x : ↥(centralizer ({z} : Set H)), π (x : H) ∈ centralizer ({π z} : Set (H ⧸ O)) :=
    fun x => by
      rw [mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.1 x.2
      rw [← map_mul, ← map_mul, this]
  let f : ↥(centralizer ({z} : Set H)) →* ↥(centralizer ({π z} : Set (H ⧸ O))) :=
    MonoidHom.codRestrict (π.comp (centralizer ({z} : Set H)).subtype)
      (centralizer ({π z} : Set (H ⧸ O))) hmem
  have hsurj : Function.Surjective f := by
    intro y
    have hyC : (y : H ⧸ O) ∈
        centralizer ((((zpowers z).map π : Subgroup (H ⧸ O))) : Set (H ⧸ O)) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
      have hc : (y : H ⧸ O) * π z = π z * (y : H ⧸ O) := mem_centralizer_singleton_iff.1 y.2
      rw [map_zpow]
      exact (Commute.zpow_left (show Commute (y : H ⧸ O) (π z) from hc).symm k).eq
    obtain ⟨x, hx, hxy⟩ := centralizer_map_le_map_centralizer hp O hO hz hyC
    have hxC : x ∈ centralizer ({z} : Set H) :=
      centralizer_le (Set.singleton_subset_iff.2 (mem_zpowers z)) hx
    exact ⟨⟨x, hxC⟩, Subtype.ext hxy⟩
  have hker : ¬ p ∣ Nat.card f.ker := by
    let g : f.ker →* O :=
      MonoidHom.codRestrict ((centralizer ({z} : Set H)).subtype.comp f.ker.subtype) O
      (fun x => by
        have h1 := x.2
        rw [MonoidHom.mem_ker] at h1
        have h2 : π ((x : ↥(centralizer ({z} : Set H))) : H) = 1 := congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff _).1 h2)
    have hg : Function.Injective g := fun a b hab => by
      have h' : ((g a : O) : H) = ((g b : O) : H) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h')
    have hdvd : Nat.card f.ker ∣ Nat.card O := Subgroup.card_dvd_of_injective g hg
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (hO.coprime_dvd_right hdvd)
  exact NoSimpleSec.of_surjective_coprime_ker f hsurj hker h

end Lift

section Simple

variable {X : Type*} [Group X]

theorem isSimpleGroup_of_isComponentOf {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hZ : center K = ⊥) : IsSimpleGroup K := by
  have h1 : IsSimpleGroup (K ⧸ center K) := hK.2.2.2
  have e : (K ⧸ center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  haveI := h1
  exact MulEquiv.isSimpleGroup e.symm

theorem exists_noncomm_of_isComponentOf {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', b', fun hcomm => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]

end Simple

theorem bal3NoPermute_of_schreier
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog) :
    Bal3NoPermute := by
  classical
  intro H _ _ hcat P z D hconf hemb hcon hQ K hK
  by_contra hnorm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  set O : Subgroup H := primeComplementCore (G := H) 3 with hOdef
  have hO : (3 : ℕ).Coprime (Nat.card O) := primeComplementCore_coprime 3
  set π := QuotientGroup.mk' O with hπ
  have hred := Lemma212Config.reduce (by norm_num : (3 : ℕ) ≠ 2) hconf
  have hnorm' : ¬ ((redSylow P : Sylow 3 (H ⧸ O)) : Subgroup (H ⧸ O)) ≤
      normalizer (K : Set (H ⧸ O)) := by
    rw [coe_redSylow]
    exact hnorm
  have hexK : ∃ K₁ : Subgroup (H ⧸ O), IsComponentOf K₁ ⊤ ∧
      ¬ D.map π ≤ normalizer (K₁ : Set (H ⧸ O)) := by
    by_contra hall
    push_neg at hall
    exact hnorm' (hred.le_normalizer_of_forall hQ hall hK)
  obtain ⟨K₁, hK₁, hDK₁⟩ := hexK
  obtain ⟨d, hdD, hdN⟩ := SetLike.not_le_iff_exists.1 hDK₁
  have hd3 : d ^ 3 = 1 := hred.elem.2 d hdD
  obtain ⟨K₂, K₃, hK₂eq, hK₃eq, hK₂, hK₃, h12, h13, h23, hc₃, hall⟩ :=
    orbit_three hd3 hK₁ hdN hred.card_components_le
  set c := MulAut.conj d with hcdef
  have hZ : ∀ L : Subgroup (H ⧸ O), IsComponentOf L ⊤ → center L = ⊥ := fun L hL =>
    center_eq_bot_of_isComponentOf hp3 hred.core hQ hL
  have hZ₁ := hZ K₁ hK₁
  have hZ₂ := hZ K₂ hK₂
  have hZ₃ := hZ K₃ hK₃
  have hcm : ∀ {A B : Subgroup (H ⧸ O)}, IsComponentOf A ⊤ → IsComponentOf B ⊤ → A ≠ B →
      A ≤ centralizer (B : Set (H ⧸ O)) := fun hA hB hAB =>
    commutator_eq_bot_iff_le_centralizer.mp
      (ComponentClassification.LocalComponents.commute_of_ne _ _ hA hB hAB)
  have hlayer : CFSG.layer (H ⧸ O) = K₁ ⊔ K₂ ⊔ K₃ := by
    rw [CFSG.layer.eq_sSup]
    refine le_antisymm (sSup_le fun L hL => ?_) (sup_le (sup_le ?_ ?_) ?_)
    · rcases hall L ((CFSG.isComponent_iff_open L).1 hL) with rfl | rfl | rfl
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    · exact le_sSup ((CFSG.isComponent_iff_open K₁).2 hK₁)
    · exact le_sSup ((CFSG.isComponent_iff_open K₂).2 hK₂)
    · exact le_sSup ((CFSG.isComponent_iff_open K₃).2 hK₃)
  have hzE : π z ∈ CFSG.layer (H ⧸ O) := hred.mem_layer hK₁
  have hz1 : π z ≠ 1 := by
    intro h1
    have := hred.ord
    rw [h1, orderOf_one] at this
    exact hp3.one_lt.ne this
  have hdz : d * π z = π z * d :=
    congrArg Subtype.val (hred.elem.1.is_comm.comm ⟨d, hdD⟩ ⟨π z, hred.mem⟩)
  have hc₁ : c • K₁ = K₂ := hK₂eq.symm
  have hc₂ : c • K₂ = K₃ := hK₃eq.symm
  have hw₁ : π z ∉ K₂ ⊔ K₃ :=
    not_mem_sup_of_cycle hZ hdz hK₁ hK₂ hK₃ h12 h13 h23 hall hc₁ hc₂ hc₃ hzE hz1
  have hw₃' : π z ∉ K₃ ⊔ K₁ :=
    not_mem_sup_of_cycle hZ hdz hK₂ hK₃ hK₁ h23 h12.symm h13.symm
      (fun L hL => by rcases hall L hL with h | h | h <;> simp [h]) hc₂ hc₃ hc₁ hzE hz1
  have hw₂' : π z ∉ K₁ ⊔ K₂ :=
    not_mem_sup_of_cycle hZ hdz hK₃ hK₁ hK₂ h13.symm h23.symm h12
      (fun L hL => by rcases hall L hL with h | h | h <;> simp [h]) hc₃ hc₁ hc₂ hzE hz1
  have hw₂ : π z ∉ K₁ ⊔ K₃ := by rwa [sup_comm]
  have hM : NoSimpleSec 3 ↥((centralizer ({π z} : Set (H ⧸ O))) ⊓ CFSG.layer (H ⧸ O)) := by
    rw [hlayer]
    exact noSimpleSec_centralizer_inf_layer hred.core hred.pRank_top.le hK₁ hK₂ hK₃ h12 h13 h23
      hZ₁ hZ₂ hZ₃ (hlayer ▸ hzE) hred.ord hw₁ hw₂ hw₂'
  haveI hch : (CFSG.layer (H ⧸ O)).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI : (CFSG.layer (H ⧸ O)).Normal := inferInstance
  have hX : CatalogSimpleSections (H ⧸ O) := hcat.quotient _
  have hF : CFSG.fittingSubgroup (H ⧸ O) = ⊥ := by
    rw [CFSG.Fitting_eq_pcore _ 3 hred.core, hQ]
  have hSolv : Group.IsSolvable ((H ⧸ O) ⧸ CFSG.layer (H ⧸ O)) :=
    isSolvable_quotient_layer_of_card_components_le hSch hX hF
      (fun S hS => (hred.card_components_le S hS).trans (by norm_num)) _ rfl
  have hNc : NoSimpleSec 3 ↥(centralizer ({π z} : Set (H ⧸ O))) := by
    set C : Subgroup (H ⧸ O) := centralizer ({π z} : Set (H ⧸ O)) with hCdef
    let Φ : ↥C →* (H ⧸ O) ⧸ CFSG.layer (H ⧸ O) :=
      (QuotientGroup.mk' (CFSG.layer (H ⧸ O))).comp C.subtype
    have hY : NoSimpleSec 3 ↥Φ.range := NoSimpleSec.of_isSolvable 3
    have hK : NoSimpleSec 3 ↥Φ.rangeRestrict.ker := by
      let g : ↥Φ.rangeRestrict.ker →* ↥(C ⊓ CFSG.layer (H ⧸ O)) :=
        MonoidHom.codRestrict (C.subtype.comp Φ.rangeRestrict.ker.subtype)
          (C ⊓ CFSG.layer (H ⧸ O)) (fun x => by
            have h1 := x.2
            rw [MonoidHom.mem_ker] at h1
            have h2 : Φ ((x : ↥C)) = 1 := congrArg Subtype.val h1
            exact ⟨((x : ↥C)).2, (QuotientGroup.eq_one_iff _).1 h2⟩)
      have hg : Function.Injective g := fun a b hab => by
        have h' : ((g a : ↥(C ⊓ CFSG.layer (H ⧸ O))) : H ⧸ O) =
            ((g b : ↥(C ⊓ CFSG.layer (H ⧸ O))) : H ⧸ O) := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h')
      exact NoSimpleSec.of_injective g hg hM
    exact NoSimpleSec.of_surjective_ker Φ.rangeRestrict Φ.rangeRestrict_surjective hK hY
  have hzp : IsPGroup 3 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hconf.ord, pow_one])
  have hCz : NoSimpleSec 3 ↥(centralizer ({z} : Set H)) :=
    noSimpleSec_centralizer_of_quotient hp3 O hO hzp hNc
  obtain ⟨d₀, hd₀D, hd₀d⟩ := hdD
  have hd₀z : d₀ ∉ zpowers z := by
    intro hmem
    have hdz' : d ∈ zpowers (π z) := by
      rw [← hd₀d, ← MonoidHom.map_zpowers]
      exact mem_map_of_mem π hmem
    have hzlayer : zpowers (π z) ≤ CFSG.layer (H ⧸ O) := zpowers_le.2 hzE
    exact hdN (CFSG.LocalCores.layer_le_normalizer ((CFSG.isComponent_iff_open K₁).2 hK₁)
      (hzlayer hdz'))
  obtain ⟨f, hf⟩ := hemb d₀ hd₀D hd₀z
  have hCd : NoSimpleSec 3 ↥(centralizer ({d₀} : Set H)) := NoSimpleSec.of_injective f hf hCz
  obtain ⟨ψ, hψ, hψC⟩ := exists_diag_hom hd3 hc₁ hc₂ (hcm hK₂ hK₁ h12.symm)
    (hcm hK₃ hK₁ h13.symm) (hcm hK₃ hK₂ h23.symm) hZ₁
  have hd₀p : IsPGroup 3 (zpowers d₀) :=
    (elementary_isPGroup 3 D hconf.elem).to_le (zpowers_le.2 hd₀D)
  haveI : IsSimpleGroup K₁ := isSimpleGroup_of_isComponentOf hK₁ hZ₁
  have hpK : 3 ∣ Nat.card K₁ :=
    (prime_dvd_card_center_quotient_of_isComponentOf hp3 hred.core hK₁).trans
      (Subgroup.card_quotient_dvd_card (center K₁))
  have hψC' : ∀ s, ψ s ∈ centralizer ({π d₀} : Set (H ⧸ O)) := by
    rw [hd₀d]
    exact hψC
  exact false_of_section_centralizer hp3 O hO hd₀p (exists_noncomm_of_isComponentOf hK₁) hpK ψ hψ
    hψC' hCd

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
