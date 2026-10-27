module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenComp
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

theorem normalizer_le_normalizer_omegaOnePSub {X : Type} [Group X] (p : ℕ) (T : Subgroup X) :
    normalizer (T : Set X) ≤ normalizer (omegaOnePSub p T : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  have hg_inv : g⁻¹ ∈ normalizer (T : Set X) := (normalizer (T : Set X)).inv_mem hg
  have key : ∀ c : X, c ∈ normalizer (T : Set X) →
      omegaOnePSub p T ≤ (omegaOnePSub p T).comap (MulAut.conj c).toMonoidHom := by
    intro c hc
    rw [omegaOnePSub]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    change c * x * c⁻¹ ∈ Subgroup.closure {y : X | y ∈ T ∧ y ^ p = 1}
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hc x).mp hx.1, ?_⟩
    rw [conj_pow, hx.2, mul_one, mul_inv_cancel]
  intro h
  constructor
  · intro hh
    exact key g hg hh
  · intro hh
    have h2 : (MulAut.conj g⁻¹).toMonoidHom (g * h * g⁻¹) ∈ omegaOnePSub p T :=
      key g⁻¹ hg_inv hh
    have heq : (MulAut.conj g⁻¹).toMonoidHom (g * h * g⁻¹) = h := by
      change (MulAut.conj g⁻¹) (g * h * g⁻¹) = h
      rw [MulAut.conj_apply]
      group
    rwa [heq] at h2

theorem layer_eq_iSup_of_components {X : Type*} [Group X] {ι : Type*} (f : ι → Subgroup X)
    (hf : ∀ D : Subgroup X, CFSG.IsComponent D ↔ ∃ i, D = f i) :
    CFSG.layer X = ⨆ i, f i := by
  rw [CFSG.layer.eq_sSup, ← sSup_range]
  congr 1
  ext D
  simp only [Set.mem_setOf_eq, Set.mem_range]
  rw [hf D]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩

theorem surjective_comp_subtype_of_top_le {X Y : Type*} [Group X] [Group Y] {φ : X →* Y}
    (hφ : Function.Surjective φ) {A B : Subgroup X} [A.Normal]
    (hAB : (⊤ : Subgroup X) ≤ A ⊔ B) (hA : A ≤ φ.ker) :
    Function.Surjective (φ.comp B.subtype) := by
  intro y
  obtain ⟨x, rfl⟩ := hφ y
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (hAB (show x ∈ (⊤ : Subgroup X) from trivial))
  refine ⟨⟨b, hb⟩, ?_⟩
  rw [← hab, map_mul, MonoidHom.mem_ker.mp (hA ha), one_mul]
  rfl

theorem conj_mem_of_mem_centralizer {X : Type*} [Group X] {L N W M : Subgroup X} [L.Normal]
    (hLN : (⊤ : Subgroup X) ≤ L ⊔ N) (hNW : N ≤ normalizer (W : Set X)) (hLM : L ≤ M)
    (hWM : centralizer (W : Set X) ≤ M) {g : X} (hg : g ∈ centralizer (W : Set X)) (h : X) :
    h * g * h⁻¹ ∈ M := by
  obtain ⟨l, hl, n, hn, hln⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (hLN (show h ∈ (⊤ : Subgroup X) from trivial))
  have hLnorm : L.Normal := inferInstance
  have hg' : n * g * n⁻¹ ∈ centralizer (W : Set X) := by
    have himage : (MulAut.conj n).toMonoidHom '' (W : Set X) = W := by
      rw [← Subgroup.coe_map]
      exact congrArg (fun P : Subgroup X => (P : Set X))
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNW hn))
    have hmap := Subgroup.map_centralizer_le_centralizer_image (W : Set X)
      (MulAut.conj n).toMonoidHom
    rw [himage] at hmap
    exact hmap (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
  have h1 : l * (n * g * n⁻¹ * l⁻¹ * (n * g * n⁻¹)⁻¹) * (n * g * n⁻¹) ∈ M :=
    M.mul_mem (hLM (L.mul_mem hl (hLnorm.conj_mem l⁻¹ (L.inv_mem hl) (n * g * n⁻¹))))
      (hWM hg')
  have hfin : h * g * h⁻¹ =
      l * (n * g * n⁻¹ * l⁻¹ * (n * g * n⁻¹)⁻¹) * (n * g * n⁻¹) := by
    rw [← hln]
    group
  rw [hfin]
  exact h1

theorem map_normalizerMonoidHom_subgroupOf {X : Type*} [Group X] (W C : Subgroup X)
    (x : normalizer (W : Set X)) :
    (C.subgroupOf W).map (W.normalizerMonoidHom x).toMonoidHom =
      (C.map (MulAut.conj (x : X)).toMonoidHom).subgroupOf W := by
  ext v
  constructor
  · intro hv
    rw [Subgroup.mem_map] at hv
    obtain ⟨w, hw, hwv⟩ := hv
    rw [Subgroup.mem_subgroupOf] at hw
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    refine ⟨(w : X), hw, ?_⟩
    exact congrArg Subtype.val hwv
  · intro hv
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hv
    obtain ⟨c, hc, hcv⟩ := hv
    rw [Subgroup.mem_map]
    have hcW : c ∈ W := by
      have hxinv := (normalizer (W : Set X)).inv_mem x.2
      have h := (Subgroup.mem_normalizer_iff.mp hxinv (v : X)).mp v.2
      have heq : (x : X)⁻¹ * (v : X) * (x : X) = c := by
        rw [← hcv]
        change (x : X)⁻¹ * ((x : X) * c * (x : X)⁻¹) * (x : X) = c
        group
      rwa [inv_inv, heq] at h
    refine ⟨⟨c, hcW⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hc
    · apply Subtype.ext
      change (MulAut.conj (x : X)).toMonoidHom c = (v : X)
      exact hcv

namespace NineSetting

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem centralizer_le_of_mem_starImg (h : NineSetting G M p Q H E 2) {x : StarGroup p H}
    (hxE : x ∈ starImg p H E) (hx1 : x ≠ 1) {V : Subgroup (StarGroup p H)} (hxV : x ∈ V) :
    centralizer (V : Set (StarGroup p H)) ≤ starImg p H M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hxE
  have huE : (u : G) ∈ E := Subgroup.mem_subgroupOf.mp hu
  have hu1 : u ≠ 1 := by
    intro h1
    exact hx1 (by rw [← hux, h1, map_one])
  have huG1 : (u : G) ≠ 1 := by
    intro h1
    exact hu1 (Subtype.ext h1)
  have hup : (u : G) ^ p = 1 := h.stdE.2.2.1.2 (u : G) huE
  have horder : orderOf (u : G) = p := orderOf_eq_prime hup huG1
  let S : Subgroup G := Subgroup.zpowers (u : G)
  have hSE : S ≤ E := Subgroup.zpowers_le.mpr huE
  have hSH : S ≤ H := hSE.trans (h.stdE.2.1.trans h.Q_le_H)
  have hSp : IsPGroup p S := (CFSG.Open.isElemAbelian_zpowers hup).isPGroup
  have hcardS : Nat.card S = p ^ 1 := by
    rw [Nat.card_zpowers, horder, pow_one]
  have h1rank : 1 ≤ CFSG.Open.pRank p S :=
    CFSG.SectionRank.le_pRank h.prime.one_lt le_rfl (CFSG.Open.isElemAbelian_zpowers hup) hcardS
  have hN : normalizer (S : Set G) ≤ M := by
    have hle : normalizer (S : Set G) ≤ rankThreeGamma 1 p E := by
      rw [show rankThreeGamma 1 p E = GLBCore p 1 E from rfl]
      unfold GLBCore
      exact le_sSup ⟨S, hSE, h1rank, rfl⟩
    exact hle.trans (by simpa using h.stdE.2.2.2.2)
  have hmap : starImg p H S = Subgroup.zpowers x := by
    have hSsub : S.subgroupOf H = Subgroup.zpowers u := by
      ext w
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j, Subtype.ext (by rw [Subgroup.coe_zpow, hj])⟩
      · rintro ⟨j, hj⟩
        exact ⟨j, by rw [← Subgroup.coe_zpow, hj]⟩
    rw [starImg, hSsub, MonoidHom.map_zpowers, hux]
  have hnorm : normalizer (Subgroup.zpowers x : Set (StarGroup p H)) ≤ starImg p H M := by
    rw [← hmap]
    exact h.normalizer_starImg_le hSH hSp hN
  have hcn : centralizer ({x} : Set (StarGroup p H)) ≤
      normalizer (Subgroup.zpowers x : Set (StarGroup p H)) := by
    refine (Subgroup.centralizer_le_normalizer {x}).trans ?_
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.normalizer_le_normalizer_closure {x}
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxV)).trans (hcn.trans hnorm)

theorem exists_hom_quotKer (h : NineSetting G M p Q H E k) :
    ∃ φ : StarGroup p H →* QuotKer M H, Function.Surjective φ ∧
      ∀ y : StarGroup p H, (∀ g : StarGroup p H, g * y * g⁻¹ ∈ starImg p H M) → φ y = 1 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let K : Subgroup ↥H := Subgroup.normalCore ((M ⊓ H).subgroupOf H)
  haveI hKn : K.Normal := inferInstance
  have hOM : ∀ u : ↥H, u ∈ O → (u : G) ∈ M := by
    intro u hu
    have h1 : (u : G) ∈ relPPrimeCore p H := by
      rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
        h.prime H]
      exact ⟨u, show u ∈ CFSG.pPrimeCore p ↥H from hu, rfl⟩
    exact h.relPPrimeCore_le h1
  have hOK : O ≤ K := by
    change O ≤ Subgroup.normalCore ((M ⊓ H).subgroupOf H)
    refine Subgroup.normal_le_normalCore.mpr fun u hu => ?_
    exact Subgroup.mem_subgroupOf.mpr ⟨hOM u hu, u.2⟩
  refine ⟨QuotientGroup.map O K (MonoidHom.id ↥H) (by simpa using hOK), ?_, ?_⟩
  · intro y
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective K y
    exact ⟨QuotientGroup.mk' O u, rfl⟩
  · intro y hy
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective O y
    have huK : u ∈ K := by
      change u ∈ Subgroup.normalCore ((M ⊓ H).subgroupOf H)
      intro b
      have hb := hy (QuotientGroup.mk' O b)
      have hb' : QuotientGroup.mk' O (b * u * b⁻¹) ∈ starImg p H M := by
        simpa only [map_mul, map_inv] using hb
      rw [starImg] at hb'
      obtain ⟨m, hmM, hmeq⟩ := Subgroup.mem_map.mp hb'
      have hmeq' : QuotientGroup.mk' O m = QuotientGroup.mk' O (b * u * b⁻¹) := hmeq
      have hzO : m⁻¹ * (b * u * b⁻¹) ∈ O := by
        rw [← QuotientGroup.eq_one_iff (N := O)]
        change QuotientGroup.mk' O (m⁻¹ * (b * u * b⁻¹)) = 1
        rw [map_mul, map_inv, hmeq', inv_mul_cancel]
      have hzM : ((m⁻¹ * (b * u * b⁻¹) : ↥H) : G) ∈ M := hOM _ hzO
      have hmMG : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hmM
      have hz : ((b * u * b⁻¹ : ↥H) : G) =
          (m : G) * ((m⁻¹ * (b * u * b⁻¹) : ↥H) : G) :=
        congrArg Subtype.val
          (by group : (b * u * b⁻¹ : ↥H) = m * (m⁻¹ * (b * u * b⁻¹)))
      refine Subgroup.mem_subgroupOf.mpr ⟨?_, (b * u * b⁻¹).2⟩
      rw [hz]
      exact M.mul_mem hmMG hzM
    rw [QuotientGroup.map_mk', QuotientGroup.eq_one_iff]
    exact huK

theorem top_le_layer_sup_normalizer (h : NineSetting G M p Q H E k)
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H) :
    (⊤ : Subgroup (StarGroup p H)) ≤ CFSG.layer (StarGroup p H) ⊔
      normalizer ((starImg p H Q ⊓ CFSG.layer (StarGroup p H) : Subgroup (StarGroup p H)) :
        Set (StarGroup p H)) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let L : Subgroup (StarGroup p H) := CFSG.layer (StarGroup p H)
  haveI hLc : L.Characteristic := by
    change (CFSG.layer (StarGroup p H)).Characteristic
    exact CFSG.LocalCores.layer_characteristic
  haveI hLn : L.Normal := inferInstance
  have hSyl : CFSG.ABGLocalTools.IsSylowOf p (starImg p H Q ⊓ L) L :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer (h.isSylowOf_starImg_top hQ) le_top
      (by simp [Subgroup.normalizer_eq_top])
  obtain ⟨S, hS⟩ := hSyl
  have hfr := Sylow.normalizer_sup_eq_top S
  rw [hS, sup_comm] at hfr
  exact le_of_eq hfr.symm

end NineSetting

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
