module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YJ

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G]

private lemma eq_one_of_mem_centralizer_of_mem {L : Subgroup G} (hZ : center ↥L = ⊥) {x : G}
    (hxL : x ∈ L) (hxC : x ∈ centralizer (L : Set G)) : x = 1 := by
  have hcenter : (⟨x, hxL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) (y : G) y.2)
  have hone : (⟨x, hxL⟩ : ↥L) = 1 := by
    rw [hZ] at hcenter
    exact Subgroup.mem_bot.mp hcenter
  exact congrArg Subtype.val hone

private lemma innerAut_normal_local (Q : Type) [Group Q] : (innerAut Q).Normal := by
  change ((MulAut.conj : Q →* MulAut Q).range).Normal
  refine ⟨?_⟩
  rintro _ ⟨k, rfl⟩ φ
  exact ⟨φ k, by ext y; simp [MulAut.conj_apply]⟩

private lemma actsAs_zpow [Finite G] {L : Subgroup G} {g : G} {σ : MulAut (L ⧸ center L)}
    (hg : ActsAs L g σ) (n : ℤ) : ActsAs L (g ^ n) (σ ^ n) := by
  obtain ⟨hgN, hj⟩ := (actsAs_iff L).mp hg
  refine (actsAs_iff L).mpr ⟨(normalizer (L : Set G)).zpow_mem hgN n, ?_⟩
  have hsub : (⟨g ^ n, (normalizer (L : Set G)).zpow_mem hgN n⟩ :
        ↥(normalizer (L : Set G))) = (⟨g, hgN⟩ : ↥(normalizer (L : Set G))) ^ n := by
    ext; simp
  rw [hsub, map_zpow, hj]

private lemma jOn_comm_fwd [Finite G] (L : Subgroup G) {g : G} {σ : MulAut (L ⧸ center L)}
    (hg : ActsAs L g σ) (l : ↥L) (hcomm : (l : G) * g = g * (l : G)) :
    jOn L (Subgroup.le_normalizer) l * σ = σ * jOn L (Subgroup.le_normalizer) l := by
  have hgN : g ∈ normalizer (L : Set G) := mem_normalizer_of_actsAs L hg
  have hg_eq : jHom L ⟨g, hgN⟩ = σ := actsAs_unique L (jHom_actsAs L ⟨g, hgN⟩) hg
  rw [show jOn L (Subgroup.le_normalizer) l =
    jHom L (Subgroup.inclusion (Subgroup.le_normalizer) l) from rfl, ← hg_eq]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simpa using hcomm

private lemma jOn_comm_bwd [Finite G] (L : Subgroup G) [Group.IsPerfect ↥L] (hZ : center ↥L = ⊥)
    {g : G} {σ : MulAut (L ⧸ center L)} (hg : ActsAs L g σ) (l : ↥L)
    (hcomm : jOn L (Subgroup.le_normalizer) l * σ = σ * jOn L (Subgroup.le_normalizer) l) :
    (l : G) * g = g * (l : G) := by
  have hgN : g ∈ normalizer (L : Set G) := mem_normalizer_of_actsAs L hg
  have hg_eq : jHom L ⟨g, hgN⟩ = σ := actsAs_unique L (jHom_actsAs L ⟨g, hgN⟩) hg
  let A : ↥(normalizer (L : Set G)) :=
    (Subgroup.inclusion (Subgroup.le_normalizer) l * ⟨g, hgN⟩)⁻¹ *
      (⟨g, hgN⟩ * Subgroup.inclusion (Subgroup.le_normalizer) l)
  have hmain : jHom L (Subgroup.inclusion (Subgroup.le_normalizer) l * ⟨g, hgN⟩) =
      jHom L (⟨g, hgN⟩ * Subgroup.inclusion (Subgroup.le_normalizer) l) := by
    rw [map_mul, map_mul, hg_eq]
    rwa [show jOn L (Subgroup.le_normalizer) l =
      jHom L (Subgroup.inclusion (Subgroup.le_normalizer) l) from rfl] at hcomm
  have hker_mem : A ∈ (jHom L).ker := by
    rw [MonoidHom.mem_ker]
    change jHom L ((Subgroup.inclusion (Subgroup.le_normalizer) l * ⟨g, hgN⟩)⁻¹ *
      (⟨g, hgN⟩ * Subgroup.inclusion (Subgroup.le_normalizer) l)) = 1
    rw [map_mul, map_inv, ← hmain, inv_mul_cancel]
  have hxc : (A : G) ∈ centralizer (L : Set G) := by
    rw [ker_jHom L] at hker_mem
    exact Subgroup.mem_subgroupOf.mp hker_mem
  have hA_eq : (A : G) = ((l : G) * g)⁻¹ * (g * (l : G)) := rfl
  have hxL : (A : G) ∈ L := by
    rw [hA_eq]
    have hconj : g⁻¹ * (l : G) * g ∈ L :=
      (Subgroup.mem_normalizer_iff''.mp hgN (l : G)).mp l.2
    have hconj' : g⁻¹ * (l : G)⁻¹ * g ∈ L := by
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using L.inv_mem hconj
    rw [show ((l : G) * g)⁻¹ * (g * (l : G)) =
      (g⁻¹ * (l : G)⁻¹ * g) * (l : G) by group]
    exact L.mul_mem hconj' l.2
  have hAcenter : (⟨(A : G), hxL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxc) (y : G) y.2)
  have hAone : (A : G) = 1 := by
    have h := hAcenter
    rw [hZ] at h
    exact congrArg Subtype.val (Subgroup.mem_bot.mp h)
  exact inv_mul_eq_one.mp (by rw [← hA_eq]; exact hAone)

theorem y6f4a_D_decomp [Finite G] {L : Subgroup G} [Group.IsPerfect ↥L] {g t : G}
    (hg2 : g ^ 2 = 1) (hgt : g * t = t * g) {σ : MulAut (L ⧸ center L)} (hg : ActsAs L g σ)
    (ht : t ∈ centralizer (L : Set G))
    (hH : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hker : ∀ x ∈ centralizer ({t} : Set G), x ∈ centralizer (L : Set G) → x ∈ zpowers t)
    (hAut : innerAut (L ⧸ center L) ⊔ closure {σ} = ⊤) (hσ2 : σ ^ 2 = 1) :
    centralizer ({g} : Set G) ⊓ centralizer ({t} : Set G) =
      centEl L g ⊔ closure ({g, t} : Set G) := by
  haveI : (innerAut (L ⧸ center L)).Normal := innerAut_normal_local _
  apply le_antisymm
  · intro h hh
    obtain ⟨hhg, hht⟩ := Subgroup.mem_inf.mp hh
    have hhN : h ∈ normalizer (L : Set G) := hH hht
    let α : MulAut (L ⧸ center L) := jHom L ⟨h, hhN⟩
    have hα : ActsAs L h α := jHom_actsAs L ⟨h, hhN⟩
    have hmem_sup : α ∈ innerAut (L ⧸ center L) ⊔
        closure ({σ} : Set (MulAut (L ⧸ center L))) := by
      rw [hAut]; exact Subgroup.mem_top α
    obtain ⟨i, hi, y, hy, hiy⟩ := Subgroup.mem_sup_of_normal_left.mp hmem_sup
    rw [← jSub_self L] at hi
    obtain ⟨l, hl, hli⟩ := (mem_jSub L).mp hi
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (by rwa [← Subgroup.zpowers_eq_closure] at hy)
    have hgzn : ActsAs L (g ^ n) (σ ^ n) := actsAs_zpow hg n
    have hu : ActsAs L (l * g ^ n) (i * σ ^ n) := actsAs_mul L hli hgzn
    have hαeq : i * σ ^ n = α := by rw [hn, hiy]
    have hx1 : ActsAs L ((l * g ^ n)⁻¹ * h) 1 := by
      have hacts := actsAs_mul L (actsAs_inv L hu) hα
      rwa [← hαeq, inv_mul_cancel] at hacts
    have hxL : (l * g ^ n)⁻¹ * h ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp hx1
    have hlCt : l ∈ centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp ht) l hl)
    have hgCt : g ∈ centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hgt
    have hgnCt : g ^ n ∈ centralizer ({t} : Set G) :=
      (centralizer ({t} : Set G)).zpow_mem hgCt n
    have hxCt : (l * g ^ n)⁻¹ * h ∈ centralizer ({t} : Set G) :=
      (centralizer ({t} : Set G)).mul_mem
        ((centralizer ({t} : Set G)).inv_mem ((centralizer ({t} : Set G)).mul_mem hlCt hgnCt))
        hht
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hker _ hxCt hxL)
    have hh_eq : h = (l * g ^ n) * t ^ a := by rw [ha]; group
    have hl_eq : l = h * t ^ (-a) * g ^ (-n) := by rw [hh_eq]; group
    have hhCg : h ∈ centralizer ({g} : Set G) := hhg
    have htCg : t ∈ centralizer ({g} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hgt.symm
    have hgCg : g ∈ centralizer ({g} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hlCg : l ∈ centralizer ({g} : Set G) := by
      rw [hl_eq]
      exact (centralizer ({g} : Set G)).mul_mem
        ((centralizer ({g} : Set G)).mul_mem hhCg
          ((centralizer ({g} : Set G)).zpow_mem htCg (-a)))
        ((centralizer ({g} : Set G)).zpow_mem hgCg (-n))
    have hlcent : l ∈ centEl L g := Subgroup.mem_inf.mpr ⟨hl, hlCg⟩
    have hgnV : g ^ n ∈ closure ({g, t} : Set G) :=
      (closure ({g, t} : Set G)).zpow_mem (Subgroup.subset_closure (by simp)) n
    have htaV : t ^ a ∈ closure ({g, t} : Set G) :=
      (closure ({g, t} : Set G)).zpow_mem (Subgroup.subset_closure (by simp)) a
    have hclosure : g ^ n * t ^ a ∈ closure ({g, t} : Set G) :=
      Subgroup.mul_mem _ hgnV htaV
    have h_eq : h = l * (g ^ n * t ^ a) := by rw [hh_eq]; group
    rw [h_eq]
    exact Subgroup.mul_mem_sup hlcent hclosure
  · apply sup_le
    · refine le_inf inf_le_right ?_
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp ht) l (Subgroup.mem_inf.mp hl).1)
    · apply le_inf
      · rw [Subgroup.closure_le]
        intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hx
        · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          exact Subgroup.mem_centralizer_singleton_iff.mpr hgt.symm
      · rw [Subgroup.closure_le]
        intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hx
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hgt
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          exact Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem y6f4a_centEl_equiv [Finite G] {L : Subgroup G} [Group.IsPerfect ↥L]
    (hZ : center ↥L = ⊥) {g : G} {σ : MulAut (L ⧸ center L)} (hg : ActsAs L g σ) :
    Nonempty (↥(centEl L g) ≃* ↥(centEl (innerAut (L ⧸ center L)) σ)) := by
  let hV : L ≤ normalizer (L : Set G) := Subgroup.le_normalizer
  have hφinj : Function.Injective (jOn L hV) := by
    intro a b hab
    have hker_mem : a * b⁻¹ ∈ (jOn L hV).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
    have hsub : a * b⁻¹ ∈ (centralizer (L : Set G)).subgroupOf L := by
      rwa [ker_jOn L hV] at hker_mem
    have hxC : ((a * b⁻¹ : ↥L) : G) ∈ centralizer (L : Set G) := Subgroup.mem_subgroupOf.mp hsub
    have hxL : ((a * b⁻¹ : ↥L) : G) ∈ L := (a * b⁻¹).2
    have h1 : ((a * b⁻¹ : ↥L) : G) = 1 := eq_one_of_mem_centralizer_of_mem hZ hxL hxC
    exact mul_inv_eq_one.mp (Subtype.ext h1)
  have hle : centEl L g ≤ L := fun x hx => (Subgroup.mem_inf.mp hx).1
  have hFmem : ∀ x : ↥(centEl L g),
      jOn L hV (Subgroup.inclusion hle x) ∈ centEl (innerAut (L ⧸ center L)) σ := by
    intro x
    obtain ⟨hxL, hxCg⟩ := Subgroup.mem_inf.mp x.2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← jSub_self L]
      exact (mem_jSub L).mpr ⟨(x : G), hxL, jOn_actsAs L hV (Subgroup.inclusion hle x)⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact jOn_comm_fwd L hg (Subgroup.inclusion hle x)
        (Subgroup.mem_centralizer_singleton_iff.mp hxCg)
  let F : ↥(centEl L g) →* ↥(centEl (innerAut (L ⧸ center L)) σ) :=
    ((jOn L hV).comp (Subgroup.inclusion hle)).codRestrict _ hFmem
  have hFinj : Function.Injective F := by
    intro x y hxy
    have h1 : jOn L hV (Subgroup.inclusion hle x) =
        jOn L hV (Subgroup.inclusion hle y) := by
      have := congrArg (fun z : ↥(centEl (innerAut (L ⧸ center L)) σ) =>
        (z : MulAut (L ⧸ center L))) hxy
      simpa [F] using this
    have h2 : Subgroup.inclusion hle x = Subgroup.inclusion hle y := hφinj h1
    exact Subtype.ext (congrArg (fun z : ↥L => (z : G)) h2)
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨hyinn, hycent⟩ := Subgroup.mem_inf.mp y.2
    have hyinn' : (y : MulAut (L ⧸ center L)) ∈ jSub L L := (jSub_self L).symm ▸ hyinn
    obtain ⟨l, hl, hlacts⟩ := (mem_jSub L).mp hyinn'
    have hcomm : jOn L hV ⟨l, hl⟩ * σ = σ * jOn L hV ⟨l, hl⟩ := by
      have hEq : jOn L hV ⟨l, hl⟩ = (y : MulAut (L ⧸ center L)) :=
        actsAs_unique L (jOn_actsAs L hV ⟨l, hl⟩) hlacts
      rw [hEq]
      exact Subgroup.mem_centralizer_singleton_iff.mp hycent
    have hcommG : l * g = g * l := jOn_comm_bwd L hZ hg ⟨l, hl⟩ hcomm
    let x : ↥(centEl L g) :=
      ⟨l, Subgroup.mem_inf.mpr ⟨hl, Subgroup.mem_centralizer_singleton_iff.mpr hcommG⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change jOn L hV (Subgroup.inclusion hle x) = (y : MulAut (L ⧸ center L))
    have hincl : Subgroup.inclusion hle x = (⟨l, hl⟩ : ↥L) := Subtype.ext rfl
    rw [hincl]
    exact actsAs_unique L (jOn_actsAs L hV ⟨l, hl⟩) hlacts
  exact ⟨MulEquiv.ofBijective F ⟨hFinj, hFsurj⟩⟩

end CFSG.OddStandard.HigherRank.YamadaG23
