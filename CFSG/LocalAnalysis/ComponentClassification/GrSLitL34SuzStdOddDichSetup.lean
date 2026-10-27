module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwapAction
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzCore
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdNormal
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Lift
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bActor
public import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
public import CFSG.GroupTheory.PerfectLeSupCenter
public import CFSG.LocalAnalysis.ComponentClassification.GSTopExclusion

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

private lemma l34SuzOdd_centralizer_le_normalizer (hS : L34SuzOddSetting A t) :
    centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G) :=
  fun _ hh => (CFSG.IsStandardSubgroup.standardComponentIsStandard hS.standard)
    |>.mem_normalizer_of_commute hS.t_mem hS.orderOf_t
      (Subgroup.mem_centralizer_singleton_iff.mp hh)

private theorem normal_of_index_eq_eight_of_perfect
    {C : Type*} [Group C] [Finite C] {K : Subgroup C}
    (hKperf : ⁅K, K⁆ = K)
    (hKsimple : IsSimpleGroup (K ⧸ Subgroup.center K))
    (hKbig : 5040 < Nat.card (K ⧸ Subgroup.center K))
    (hKindex : K.index = 8) : K.Normal := by
  let N : Subgroup C := K.normalCore
  have hNle : N ≤ K := Subgroup.normalCore_le K
  have hNnorm : N.Normal := Subgroup.normalCore_normal K
  suffices hNK : N = K by
    rw [← hNK]
    exact hNnorm
  let Nsub : Subgroup ↥K := N.subgroupOf K
  have hNsub_norm : Nsub.Normal := hNnorm.subgroupOf K
  let q : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' (Subgroup.center ↥K)
  let M : Subgroup (↥K ⧸ Subgroup.center ↥K) := Nsub.map q
  have hMnorm : M.Normal := hNsub_norm.map q (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hM | hM
  · have hNsubZ : Nsub ≤ Subgroup.center ↥K := by
      have h := (Subgroup.map_eq_bot_iff (H := Nsub) (f := q)).mp hM
      rwa [QuotientGroup.ker_mk'] at h
    have hNidx_dvd : N.index ∣ K.index.factorial :=
      Subgroup.index_normalCore_dvd_factorial_index K
    have hNrel : N.relIndex K = Nsub.index := rfl
    have hNindex_eq : N.index = Nsub.index * 8 := by
      rw [← Subgroup.relIndex_mul_index hNle, hKindex, hNrel]
    have hdvd5040 : Nsub.index ∣ 5040 := by
      have h := hNidx_dvd
      rw [hKindex, show (8:ℕ).factorial = 40320 by norm_num] at h
      rw [hNindex_eq, show (40320:ℕ) = 5040 * 8 by norm_num] at h
      exact Nat.dvd_of_mul_dvd_mul_right (k := 8) (by norm_num) h
    have hcardNsub_le : Nat.card Nsub ≤ Nat.card (Subgroup.center ↥K) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hNsubZ)
        (Subgroup.inclusion_injective hNsubZ)
    have hcard_le : Nat.card (↥K ⧸ Subgroup.center ↥K) ≤ Nsub.index := by
      have hmul1 : Nsub.index * Nat.card Nsub = Nat.card ↥K := Subgroup.index_mul_card Nsub
      have hmul2 : (Subgroup.center ↥K).index * Nat.card (Subgroup.center ↥K) = Nat.card ↥K :=
        Subgroup.index_mul_card (Subgroup.center ↥K)
      have hZidx : (Subgroup.center ↥K).index =
          Nat.card (↥K ⧸ Subgroup.center ↥K) := Subgroup.index_eq_card _
      have hstep : Nat.card (↥K ⧸ Subgroup.center ↥K) * Nat.card Nsub ≤
          Nsub.index * Nat.card Nsub := by
        calc Nat.card (↥K ⧸ Subgroup.center ↥K) * Nat.card Nsub
            ≤ Nat.card (↥K ⧸ Subgroup.center ↥K) * Nat.card (Subgroup.center ↥K) :=
              Nat.mul_le_mul_left _ hcardNsub_le
          _ = Nat.card ↥K := by rw [← hZidx, hmul2]
          _ = Nsub.index * Nat.card Nsub := hmul1.symm
      exact Nat.le_of_mul_le_mul_right hstep (Nat.card_pos)
    have hle5040 : Nsub.index ≤ 5040 := Nat.le_of_dvd (by norm_num) hdvd5040
    omega
  · have hsup : Nsub ⊔ Subgroup.center ↥K = ⊤ := by
      have hrange : q.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
      have h := (Subgroup.map_eq_range_iff (f := q) (H := Nsub)).mp (hM.trans hrange.symm)
      rw [QuotientGroup.ker_mk'] at h
      exact codisjoint_iff.mp h
    have hperfK : commutator ↥K = ⊤ :=
      Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hKperf)
    have hNsub_top : Nsub = ⊤ :=
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.eq_top_of_sup_center_eq_top hperfK hsup
    have hKleN : K ≤ N := Subgroup.subgroupOf_eq_top.mp (by simpa [Nsub] using hNsub_top)
    exact le_antisymm hNle hKleN

theorem mem_centralizer_of_l34SuzOdd (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) : t ∈ centralizer ({u} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 hS.t_mem u (hD.le_A hu)).symm

omit [Finite G] in
theorem isQuasisimple_of_l34SuzOdd (hD : L34SuzOddData A V K y) : IsQuasisimple ↥K := by
  have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hD.perfect
  have hsimple : IsSimpleGroup (↥K ⧸ center ↥K) :=
    Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hD.l34
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).1
    ⟨hperf.commutator_eq_top, hsimple⟩

theorem isKGroupCat_centralizer_of_l34SuzOdd (hS : L34SuzOddSetting A t) {u : G} (hu1 : u ≠ 1) :
    SectionRank.IsKGroupCat ↥(centralizer ({u} : Set G)) := by
  have htop : centralizer ({u} : Set G) ≠ ⊤ := by
    intro hc
    have huZ : u ∈ center G :=
      Set.singleton_subset_iff.1 ((Subgroup.centralizer_eq_top_iff_subset).1 hc)
    have hctop : center G = ⊤ := by
      rcases hS.base.1.eq_bot_or_eq_top_of_normal (center G) with hbot | htop
      · exact absurd (hbot ▸ huZ) (by simp [Subgroup.mem_bot, hu1])
      · exact htop
    have hcomm : IsMulCommutative G := Subgroup.center_eq_top_iff.1 hctop
    obtain ⟨x, y, hxy⟩ := hS.base.2.1
    exact hxy (isMulCommutative_iff.mp hcomm x y)
  exact GSThmB.isKGroupCat_of_ne_top' hS.base.2.2.1 htop

omit [Finite G] in
theorem isQuasisimple_subgroupOf_of_l34SuzOdd (hD : L34SuzOddData A V K y) {u : G}
    (hu : u ∈ V) :
    IsQuasisimple ↥(K.subgroupOf (centralizer ({u} : Set G))) :=
  (IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe (le_centralizer_of_l34SuzOddData hD hu))).mpr
    (isQuasisimple_of_l34SuzOdd hD)

theorem odd_card_center_subgroupOf_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) :
    Odd (Nat.card (center ↥(K.subgroupOf (centralizer ({u} : Set G))))) := by
  rw [Nat.card_congr (Subgroup.centerCongr
    (Subgroup.subgroupOfEquivOfLe (le_centralizer_of_l34SuzOddData hD hu))).toEquiv]
  exact odd_card_center_of_l34SuzOdd hS hD

omit [Finite G] in
theorem isL34Type_subgroupOf_of_l34SuzOdd (hD : L34SuzOddData A V K y) {u : G}
    (hu : u ∈ V) :
    IsL34Type (↥(K.subgroupOf (centralizer ({u} : Set G))) ⧸
      center ↥(K.subgroupOf (centralizer ({u} : Set G)))) := by
  let e : ↥(K.subgroupOf (centralizer ({u} : Set G))) ≃* ↥K :=
    Subgroup.subgroupOfEquivOfLe (le_centralizer_of_l34SuzOddData hD hu)
  exact hD.l34.of_mulEquiv
    (QuotientGroup.congr (center ↥(K.subgroupOf (centralizer ({u} : Set G)))) (center ↥K) e
      (Subgroup.map_center_eq e)).symm

section Certified


theorem normal_subgroupOf_of_l34SuzOdd (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1)
    (ht : t ∈ centralizer ({u} : Set G)) :
    K.subgroupOf (centralizer ({u} : Set G)) ≤
        centralizer ({(⟨t, ht⟩ : ↥(centralizer ({u} : Set G)))} : Set ↥(centralizer ({u} : Set G))) ∧
      ((K.subgroupOf (centralizer ({u} : Set G))).subgroupOf
        (centralizer ({(⟨t, ht⟩ : ↥(centralizer ({u} : Set G)))} : Set ↥(centralizer ({u} : Set G))))).Normal := by
  classical
  let X : Subgroup G := Subgroup.centralizer ({u} : Set G)
  have hKX : K ≤ X := le_centralizer_of_l34SuzOddData hD hu
  have hKA : K ≤ A := le_A_of_l34SuzOddData hD
  let tX : ↥X := ⟨t, ht⟩
  let C : Subgroup ↥X := Subgroup.centralizer ({tX} : Set ↥X)
  have hKXC : K.subgroupOf X ≤ C := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hS.t_mem (k : G)
      (hKA (Subgroup.mem_subgroupOf.mp hk))
  constructor
  · exact hKXC
  ·
    let uA : ↥A := ⟨u, hD.le_A hu⟩
    let qA : ↥A →* (↥A ⧸ Subgroup.center ↥A) := QuotientGroup.mk' (Subgroup.center ↥A)
    let Cbar : Subgroup (↥A ⧸ Subgroup.center ↥A) :=
      Subgroup.centralizer ({qA uA} : Set (↥A ⧸ Subgroup.center ↥A))
    let Kbar : Subgroup (↥A ⧸ Subgroup.center ↥A) := (K.subgroupOf A).map qA
    have hKsubq : IsQuasisimple ↥(K.subgroupOf A) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKA).symm
        (isQuasisimple_of_l34SuzOdd hD)
    have hKbar_card : Nat.card ↥Kbar = 20160 := by
      simpa [Kbar, qA] using hD.card_image
    have hCbar_card : Nat.card ↥Cbar = 161280 := by
      simpa [Cbar, uA, qA] using hD.card_centralizer u hu hu1
    have hKbar_le_Cbar : Kbar ≤ Cbar := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      change (x : G) * u = u * (x : G)
      have hkx : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_l34SuzOddData hD hu hkx)
    let f : ↥(K.subgroupOf A) →* (↥A ⧸ Subgroup.center ↥A) :=
      qA.comp (K.subgroupOf A).subtype
    have hfrange : f.range = Kbar := by
      ext y
      constructor
      · rintro ⟨x, -, rfl⟩
        exact Subgroup.mem_map.mpr ⟨(x : ↥A), x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    have hfne : f.range ≠ ⊥ := by
      rw [hfrange]
      intro hbot
      have := hKbar_card
      rw [hbot, Subgroup.card_bot] at this
      norm_num at this
    obtain ⟨hKbarq, ⟨eZ⟩⟩ :=
      CFSG.QuasithinUnique.Setup.X5.quasisimple_range_centerQuotientEquiv hKsubq f hfne
    have hKbarq' : IsQuasisimple ↥Kbar := hfrange ▸ hKbarq
    have hKbarperf : ⁅Kbar, Kbar⁆ = Kbar := Subgroup.isPerfect_iff.mp hKbarq'.1
    have hKbarsimple : IsSimpleGroup (Kbar ⧸ Subgroup.center Kbar) := hKbarq'.2.1
    have hKbarbig : 5040 < Nat.card (Kbar ⧸ Subgroup.center Kbar) := by
      have eZ' : Kbar ⧸ Subgroup.center Kbar ≃*
          (K.subgroupOf A) ⧸ Subgroup.center ↥(K.subgroupOf A) := hfrange ▸ eZ
      have e2 : (K.subgroupOf A) ⧸ Subgroup.center ↥(K.subgroupOf A) ≃*
          K ⧸ Subgroup.center ↥K :=
        QuotientGroup.congr (Subgroup.center ↥(K.subgroupOf A)) (Subgroup.center ↥K)
          (Subgroup.subgroupOfEquivOfLe hKA) (Subgroup.map_center_eq _)
      rw [Nat.card_congr eZ'.toEquiv, Nat.card_congr e2.toEquiv,
        CFSG.ComponentClassification.CatLeaf.card_of_isL34Type hD.l34]
      norm_num
    have hKbar_normal : (Kbar.subgroupOf Cbar).Normal := by
      let Kbar' : Subgroup ↥Cbar := Kbar.subgroupOf Cbar
      have hcardKbar' : Nat.card ↥Kbar' = 20160 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKbar_le_Cbar).toEquiv, hKbar_card]
      have hcardCbar : Nat.card ↥Cbar = 161280 := hCbar_card
      have hKbar'index : Kbar'.index = 8 := by
        have hmul : Kbar'.index * Nat.card Kbar' = Nat.card ↥Cbar := Subgroup.index_mul_card Kbar'
        rw [hcardKbar', hcardCbar] at hmul
        have h8 : Kbar'.index * 20160 = 8 * 20160 := by rw [hmul]
        exact Nat.eq_of_mul_eq_mul_right (by norm_num) h8
      have hKbar'perf : ⁅Kbar', Kbar'⁆ = Kbar' := by
        apply Subgroup.map_injective Cbar.subtype_injective
        rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
          inf_of_le_left hKbar_le_Cbar, hKbarperf]
      let ebar : ↥Kbar' ≃* ↥Kbar := Subgroup.subgroupOfEquivOfLe hKbar_le_Cbar
      have hKbar'simple : IsSimpleGroup (Kbar' ⧸ Subgroup.center Kbar') :=
        (MulEquiv.isSimpleGroup_congr (QuotientGroup.congr (Subgroup.center Kbar')
          (Subgroup.center Kbar) ebar (Subgroup.map_center_eq ebar))).mpr hKbarsimple
      have hKbar'big : 5040 < Nat.card (Kbar' ⧸ Subgroup.center Kbar') := by
        rw [Nat.card_congr (QuotientGroup.congr (Subgroup.center Kbar')
          (Subgroup.center Kbar) ebar (Subgroup.map_center_eq ebar)).toEquiv]
        exact hKbarbig
      have := normal_of_index_eq_eight_of_perfect hKbar'perf hKbar'simple hKbar'big hKbar'index
      simpa [Kbar'] using this
    have hCbar_norm : Cbar ≤ Subgroup.normalizer (Kbar : Set (↥A ⧸ Subgroup.center ↥A)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKbar_le_Cbar).mp hKbar_normal
    have hKbar_relindex : Kbar.relIndex Cbar = 2 ^ 3 := by
      have h : (Kbar.subgroupOf Cbar).index = 8 := by
        have hcardKbar' : Nat.card ↥(Kbar.subgroupOf Cbar) = 20160 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKbar_le_Cbar).toEquiv, hKbar_card]
        have hmul : (Kbar.subgroupOf Cbar).index * Nat.card ↥(Kbar.subgroupOf Cbar) =
            Nat.card ↥Cbar := Subgroup.index_mul_card (Kbar.subgroupOf Cbar)
        rw [hcardKbar', hCbar_card] at hmul
        have h8 : (Kbar.subgroupOf Cbar).index * 20160 = 8 * 20160 := by rw [hmul]
        exact Nat.eq_of_mul_eq_mul_right (by norm_num) h8
      rw [show Kbar.relIndex Cbar = (Kbar.subgroupOf Cbar).index from rfl, h]
      norm_num
    have hInv : ∀ g : ↥X, g ∈ C → K.map (MulAut.conj ((g : ↥X) : G)).toMonoidHom ≤ K := by
      intro g hg
      have hgT : ((g : ↥X) : G) * t = t * ((g : ↥X) : G) := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hg
        simpa using congrArg Subtype.val h
      have hgnorm : ((g : ↥X) : G) ∈ Subgroup.normalizer (A : Set G) :=
        l34SuzOdd_centralizer_le_normalizer hS (Subgroup.mem_centralizer_singleton_iff.mpr hgT)
      let Kg : Subgroup G := K.map (MulAut.conj ((g : ↥X) : G)).toMonoidHom
      have hKgA : Kg ≤ A := by
        calc Kg ≤ A.map (MulAut.conj ((g : ↥X) : G)).toMonoidHom := Subgroup.map_mono hKA
          _ = A := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgnorm
      have hKgperf : ⁅Kg, Kg⁆ = Kg := by
        rw [show Kg = K.map (MulAut.conj ((g : ↥X) : G)).toMonoidHom from rfl,
          ← Subgroup.map_commutator, hD.perfect]
      have hKgsubperf : ⁅Kg.subgroupOf A, Kg.subgroupOf A⁆ = Kg.subgroupOf A := by
        apply Subgroup.map_injective A.subtype_injective
        rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hKgA,
          hKgperf]
      let H : Subgroup (↥A ⧸ Subgroup.center ↥A) := (Kg.subgroupOf A).map qA
      have hHperf : ⁅H, H⁆ = H := by
        rw [show H = (Kg.subgroupOf A).map qA from rfl, ← Subgroup.map_commutator, hKgsubperf]
      have hHleCbar : H ≤ Cbar := by
        rintro y ⟨x, hx, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        change (x : G) * u = u * (x : G)
        have hxKg : (x : G) ∈ Kg := Subgroup.mem_subgroupOf.mp hx
        obtain ⟨n, hn, hxn⟩ := Subgroup.mem_map.mp hxKg
        have hgu : ((g : ↥X) : G) * u = u * ((g : ↥X) : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp g.2
        have hgu' : ((g : ↥X) : G)⁻¹ * u = u * ((g : ↥X) : G)⁻¹ := by
          calc ((g : ↥X) : G)⁻¹ * u
              = ((g : ↥X) : G)⁻¹ * (u * ((g : ↥X) : G)) * ((g : ↥X) : G)⁻¹ := by group
            _ = ((g : ↥X) : G)⁻¹ * (((g : ↥X) : G) * u) * ((g : ↥X) : G)⁻¹ := by
                rw [← hgu]
            _ = u * ((g : ↥X) : G)⁻¹ := by group
        have hKu : u ∈ Subgroup.centralizer (K : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro m hm
          exact Subgroup.mem_centralizer_singleton_iff.mp
            (le_centralizer_of_l34SuzOddData hD hu hm)
        have hnu : n * u = u * n := Subgroup.mem_centralizer_iff.mp hKu n hn
        rw [← hxn]
        calc ((g : ↥X) : G) * n * ((g : ↥X) : G)⁻¹ * u
            = ((g : ↥X) : G) * n * (((g : ↥X) : G)⁻¹ * u) := by group
          _ = ((g : ↥X) : G) * n * (u * ((g : ↥X) : G)⁻¹) := by rw [hgu']
          _ = ((g : ↥X) : G) * (n * u) * ((g : ↥X) : G)⁻¹ := by group
          _ = ((g : ↥X) : G) * (u * n) * ((g : ↥X) : G)⁻¹ := by rw [hnu]
          _ = u * (((g : ↥X) : G) * n * ((g : ↥X) : G)⁻¹) := by
            rw [← mul_assoc, hgu]; group
      have hHleKbar : H ≤ Kbar :=
        Subgroup.le_of_commutator_eq_self_of_relIndex_eq_prime_pow (p := 2) (k := 3)
          Nat.prime_two hKbar_le_Cbar hCbar_norm hKbar_relindex hHleCbar hHperf
      have hKgsub_le : Kg.subgroupOf A ≤ (K.subgroupOf A) ⊔ Subgroup.center ↥A := by
        intro x hx
        have hHx : qA x ∈ Kbar := hHleKbar (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
        obtain ⟨k, hk, hqk⟩ := Subgroup.mem_map.mp hHx
        have hz : (k : ↥A)⁻¹ * x ∈ Subgroup.center ↥A := by
          rw [← QuotientGroup.eq_one_iff]
          change qA ((k : ↥A)⁻¹ * x) = 1
          rw [map_mul, map_inv, hqk, inv_mul_cancel]
        exact Subgroup.mem_sup_of_normal_right.mpr
          ⟨k, hk, (k : ↥A)⁻¹ * x, hz, by group⟩
      have hKsubperf : ⁅K.subgroupOf A, K.subgroupOf A⁆ = K.subgroupOf A := by
        apply Subgroup.map_injective A.subtype_injective
        rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hKA,
          hD.perfect]
      have hle : Kg.subgroupOf A ≤ K.subgroupOf A :=
        CFSG.le_of_perfect_of_le_sup_center hKsubperf hKgsubperf hKgsub_le
      intro y hy
      have hyA : y ∈ A := hKgA hy
      have : (⟨y, hyA⟩ : ↥A) ∈ K.subgroupOf A := hle (show (⟨y, hyA⟩ : ↥A) ∈ Kg.subgroupOf A from hy)
      exact Subgroup.mem_subgroupOf.mp this
    refine Subgroup.Normal.mk ?_
    intro n hn g
    have hnK : ((n : ↥X) : G) ∈ K :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hn)
    have hgKg : ((g : ↥X) : G) * ((n : ↥X) : G) * (((g : ↥X) : G)⁻¹) ∈ K :=
      hInv g g.2 (Subgroup.mem_map.mpr ⟨((n : ↥X) : G), hnK, rfl⟩)
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hgKg))

end Certified

theorem wGroup_eq_bot_of_l34SuzOdd (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hC4 : SuzONanNotProperFixedCatalog) (hSV : L34SuzSignalizerVanishing)
    (hS : L34SuzOddSetting A t) {F : Subgroup G} (hFt : F ≤ centralizer ({t} : Set G))
    (hF : Open.IsElemAbelian 2 F) (hF8 : 8 ≤ Nat.card F) : wGroup F = ⊥ := by
  have hOtop : pPrimeCore 2 ↥A ≠ ⊤ := by
    intro htop
    have hodd : Odd (Nat.card ↥A) := by
      have hc := pPrimeCore_coprime_card (p := 2) (G := ↥A)
      rw [htop, Subgroup.card_top] at hc
      exact Nat.coprime_two_left.mp hc
    have hnt : Nontrivial ↥A := by
      obtain ⟨a, b, hab⟩ := hS.standard.1.2.2
      have ha1 : a ≠ 1 := fun h => hab (by rw [h, one_mul, mul_one])
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective a
      exact ⟨x, 1, fun h => ha1 (by simpa [h] using hx.symm)⟩
    have hperfect : Group.IsPerfect ↥A := hS.standard.1.1
    exact @Group.IsPerfect.not_isSolvable ↥A _ hnt hperfect (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have hZ : Open.fusionZStar ↥A = center ↥A :=
    CFSG.ComponentClassification.CatLeaf.fusionZStar_eq_center_of_quasisimple
      hS.standard.1 hOtop
  have htype : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ Open.fusionZStar ↥A) .Suz := by
    obtain ⟨eS⟩ := hS.suz
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans eS⟩
  obtain ⟨hAt, hAp, hAn⟩ :=
    le_centralizer_isPComponent_normal_of_isStandardSubgroup hS.standard hS.orderOf_t hS.t_mem
  have hsimpleG : IsSimpleGroup G := hS.base.1
  have hmirror : FooteLit.GSMirrorMaximal A :=
    @CFSG.ComponentClassification.Foote5.SolMax.gsMirrorMaximal_of_suzONan G _ _ hSch hC4
      hsimpleG hS.base.2.1 hS.base.2.2.1 A (Or.inl htype)
  have hsetting : L34NormalSettingAt
      (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t A :=
    ⟨hS.base, hS.orderOf_t, hAt, hAp, hAn, hmirror, htype⟩
  exact hSV G t A hsetting F hFt hF hF8

end CFSG.ComponentClassification.GrSLit.L34Sec5S
