module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7Defs
public import CFSG.GH74.Generic.BProg.B2.GenLoc4Defs
public import CFSG.GH74.Generic.BProg.B3.Obs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

theorem le_normalizer_of_forall_comm {X : Type*} [Group X] {H K : Subgroup X}
    (h : ∀ g ∈ K, ∀ x ∈ H, g * x = x * g) : K ≤ normalizer (H : Set X) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h g hg x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h2 := h g⁻¹ (inv_mem hg) _ hx
    have hx' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [hx', h2, inv_mul_cancel_right]
    exact hx

theorem exists_compl_zpowers {Y : Type} [Group Y] [Finite Y] {B : Subgroup Y} {z : Y}
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hzB : z ∈ B) :
    ∃ D : Subgroup Y, D ≤ B ∧ D ⊓ zpowers z = ⊥ ∧ D ⊔ zpowers z = B := by
  classical
  obtain ⟨hcomm, hsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have : Finite (Subgroup Y) :=
    Finite.of_injective (SetLike.coe : Subgroup Y → Set Y) SetLike.coe_injective
  let _ : Fintype (Subgroup Y) := Fintype.ofFinite _
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun C : Subgroup Y => C ≤ B ∧ C ⊓ zpowers z = ⊥)
    (fun C : Subgroup Y => Nat.card C) ⟨⊥, by simp⟩
  obtain ⟨hCB, hCU⟩ := (Finset.mem_filter.mp hC).2
  have hUB : zpowers z ≤ B := zpowers_le.mpr hzB
  refine ⟨C, hCB, hCU, ?_⟩
  by_contra hne
  obtain ⟨e, heB, heCU⟩ : ∃ e ∈ B, e ∉ C ⊔ zpowers z := by
    by_contra h
    push Not at h
    exact hne (le_antisymm (sup_le hCB hUB) h)
  have he2 : e * e = 1 := hsq e heB
  have hZE : zpowers e ≤ B := zpowers_le.mpr heB
  have hN : zpowers e ≤ normalizer (C : Set Y) :=
    le_normalizer_of_forall_comm fun g hg x hx => hcomm g (hZE hg) x (hCB hx)
  have hC'B : C ⊔ zpowers e ≤ B := sup_le hCB hZE
  have hC'U : (C ⊔ zpowers e) ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx1' : x ∈ ((C ⊔ zpowers e : Subgroup Y) : Set Y) := hx1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left C (zpowers e) hN] at hx1'
    obtain ⟨c, hc, b, hb, rfl⟩ := Set.mem_mul.mp hx1'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hsq' : e ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact he2
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rw [zpow_mul, hsq', one_zpow, mul_one] at hx2 ⊢
      have : c ∈ C ⊓ zpowers z := ⟨hc, hx2⟩
      rw [hCU] at this
      exact this
    · exfalso
      rw [zpow_add_one, zpow_mul, hsq', one_zpow, one_mul] at hx2
      apply heCU
      have : e = c⁻¹ * (c * e) := by group
      rw [this]
      exact mul_mem (mem_sup_left (inv_mem hc)) (mem_sup_right hx2)
  have hlt : C < C ⊔ zpowers e :=
    lt_of_le_of_ne le_sup_left fun h => heCU (mem_sup_left (h ▸ mem_sup_right (mem_zpowers e)))
  have h2 := Obs.two_mul_card_le_of_lt hlt
  have hC'mem : C ⊔ zpowers e ∈ Finset.univ.filter
      (fun C : Subgroup Y => C ≤ B ∧ C ⊓ zpowers z = ⊥) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC'B, hC'U⟩
  have h3 := hmax _ hC'mem
  have hpos : 0 < Nat.card ↥C := Nat.card_pos
  omega

theorem compl_facts {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y} {z : Y}
    (hs : Setting125 Y L B X₀ z) {D : Subgroup Y} (hDB : D ≤ B) (hDz : D ⊓ zpowers z = ⊥)
    (hDsup : D ⊔ zpowers z = B) :
    pRank 2 ↥D = 3 ∧ ∀ E : Subgroup Y, E ≤ D → 2 ≤ pRank 2 ↥E → 3 ≤ pRank 2 ↥(E ⊔ zpowers z) := by
  classical
  obtain ⟨-, hsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hs.B_el
  have hz2 : z * z = 1 := hsq z hs.z_mem
  have hzcard : Nat.card ↥(zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hz2) hs.z_ne
  have htriv : ∀ {E : Subgroup Y}, E ≤ D → ∀ x ∈ E, x ∈ zpowers z → x = 1 := by
    intro E hED x hxE hxz
    have : x ∈ D ⊓ zpowers z := ⟨hED hxE, hxz⟩
    rw [hDz] at this
    exact this
  have hBcard : Nat.card ↥B = 2 ^ 4 := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hs.B_el, hs.B_rank]
  have hDel : CFSG.IsElementaryAbelian 2 ↥D := Th2Sig6.isElementaryAbelian_of_le hs.B_el hDB
  have hle : Nat.card ↥D * 2 ≤ 2 ^ 4 := by
    have := Obs.card_mul_le_of_trivial_inter hDB (zpowers_le.mpr hs.z_mem) (htriv le_rfl)
    rwa [hzcard, hBcard] at this
  have hge : 2 ^ 4 ≤ Nat.card ↥D * 2 := by
    rw [← hBcard, ← hzcard, ← Nat.card_prod]
    refine Nat.card_le_card_of_surjective (fun p : ↥D × ↥(zpowers z) =>
      (⟨(p.1 : Y) * (p.2 : Y), hDsup ▸ mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩ : ↥B))
      ?_
    rintro ⟨b, hb⟩
    have hN : zpowers z ≤ normalizer (D : Set Y) :=
      le_normalizer_of_forall_comm fun g hg x hx =>
        ((C3.Layer1.Back.forall_of_isElementaryAbelian hs.B_el).1 g
          (zpowers_le.mpr hs.z_mem hg) x (hDB hx))
    have hb' : b ∈ ((D ⊔ zpowers z : Subgroup Y) : Set Y) := hDsup ▸ hb
    rw [Subgroup.coe_mul_of_right_le_normalizer_left D (zpowers z) hN] at hb'
    obtain ⟨d, hd, c, hc, rfl⟩ := Set.mem_mul.mp hb'
    exact ⟨(⟨d, hd⟩, ⟨c, hc⟩), rfl⟩
  have hDcard : Nat.card ↥D = 2 ^ 3 := by omega
  refine ⟨CFSG.pRank_eq_of_card_eq_pow one_lt_two hDcard, fun E hED hE2 => ?_⟩
  have hEel : CFSG.IsElementaryAbelian 2 ↥E := Th2Sig6.isElementaryAbelian_of_le hDel hED
  have hE'B : E ⊔ zpowers z ≤ B := sup_le (hED.trans hDB) (zpowers_le.mpr hs.z_mem)
  have hE'el : CFSG.IsElementaryAbelian 2 ↥(E ⊔ zpowers z) :=
    Th2Sig6.isElementaryAbelian_of_le hs.B_el hE'B
  have h1 := Obs.card_mul_le_of_trivial_inter (le_sup_left : E ≤ E ⊔ zpowers z) le_sup_right
    (htriv hED)
  rw [C3.Layer1.Back.card_eq_two_pow_pRank hEel, C3.Layer1.Back.card_eq_two_pow_pRank hE'el,
    hzcard] at h1
  by_contra hlt
  push Not at hlt
  have h4 : 2 ^ pRank 2 ↥(E ⊔ zpowers z) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 2 ^ 2 ≤ 2 ^ pRank 2 ↥E := Nat.pow_le_pow_right (by norm_num) hE2
  omega

theorem le_X₀ {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y} {z : Y}
    (hs : Setting125 Y L B X₀ z) : B ≤ X₀ := by
  have hNB : normalizer (B : Set Y) ≤ gammaK 2 B 3 :=
    le_iSup₂_of_le B le_rfl (le_iSup_of_le (by rw [hs.B_rank]; norm_num) le_rfl)
  exact (Subgroup.le_normalizer.trans hNB).trans hs.gamma

theorem false_of_weakSig2NormG4 {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y} {z : Y}
    (hs : Setting125 Y L B X₀ z) (hsig : Sig125 L X₀) (hBN : B ≤ normalizer (L : Set Y))
    (hW : B2.WeakSig2NormG4 ↥L) : False := by
  obtain ⟨D, hDB, hDz, hDsup⟩ := exists_compl_zpowers hs.B_el hs.z_mem
  obtain ⟨hDr, hEr⟩ := compl_facts hs hDB hDz hDsup
  have hDel : CFSG.IsElementaryAbelian 2 ↥D := Th2Sig6.isElementaryAbelian_of_le hs.B_el hDB
  set W : Subgroup Y := pPrimeCoreOf 2 X₀ with hWdef
  have hWodd : Odd (Nat.card ↥W) := by
    rw [hWdef, pPrimeCoreOf, Subgroup.card_map_of_injective X₀.subtype_injective]
    exact TwoThin.odd_card_pPrimeCore _
  have hXW : X₀ ≤ normalizer (W : Set Y) := fun x hx =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hx)
  have hDW : D ≤ normalizer (W : Set Y) := hDB.trans ((le_X₀ hs).trans hXW)
  have hΓ : ∀ E : Subgroup Y, E ≤ D → pRank 2 ↥D - 1 ≤ pRank 2 ↥E →
      centralizer (E : Set Y) ≤ normalizer (W : Set Y) := by
    intro E hED hE g hg
    have hE' : 3 ≤ pRank 2 ↥(E ⊔ zpowers z) := hEr E hED (by omega)
    have hE'B : E ⊔ zpowers z ≤ B := sup_le (hED.trans hDB) (zpowers_le.mpr hs.z_mem)
    have hle : E ⊔ zpowers z ≤ centralizer ({g} : Set Y) := by
      refine sup_le (fun e he => mem_centralizer_singleton_iff.mpr ?_) (zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_iff.mp hg e he
      · exact mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hs.z_cent g).symm
    have hgc : g ∈ centralizer ((E ⊔ zpowers z : Subgroup Y) : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hle hh)
    have hNE : normalizer ((E ⊔ zpowers z : Subgroup Y) : Set Y) ≤ gammaK 2 B 3 :=
      le_iSup₂_of_le (E ⊔ zpowers z) hE'B (le_iSup_of_le hE' le_rfl)
    exact hXW (hs.gamma (hNE (Subgroup.centralizer_le_normalizer _ hgc)))
  have hWC := hW Y hs.core hs.sec4 L hs.comp ⟨MulEquiv.refl _⟩ D W hDel (Or.inr hDr) hWodd hDW
    hΓ (hDB.trans hBN)
  obtain ⟨w, hwW, -, hwC⟩ := hsig
  exact hwC (hWC hwW)

theorem normal_of_rankCertified {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (h4 : SectionalTwoRankLE Y 4) (hL : CFSG.IsComponent L)
    (hc : RankCertified (↥L ⧸ center ↥L) 2) (b : Y) : b ∈ normalizer (L : Set Y) := by
  classical
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set L' : Subgroup Y := L.map (MulAut.conj b).toMonoidHom with hL'
  have hL'c : CFSG.IsComponent L' := CFSG.LocalCores.isComponent_map_mulEquiv _ hL
  have hcomm : ⁅L, L'⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hL hL'c with h | h
    · exact absurd h.symm hne
    · exact h
  have hc' : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x := fun x hx y hy => by
    have h1 : ⁅x, y⁆ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  let e : ↥L ≃* ↥L' := L.equivMapOfInjective _ (MulAut.conj b).injective
  let eq : (↥L ⧸ center ↥L) ≃* (↥L' ⧸ center ↥L') :=
    QuotientGroup.congr (center ↥L) (center ↥L') e (Subgroup.map_center_eq e)
  have hc2 : RankCertified ((↥L ⧸ center ↥L) × (↥L' ⧸ center ↥L')) 5 :=
    hc.prod (hc.of_mulEquiv eq)
  let μ : ↥L × ↥L' →* Y :=
    { toFun := fun p => (p.1 : Y) * (p.2 : Y)
      map_one' := by simp
      map_mul' := fun p q => by
        change ((p.1 : Y) * q.1) * ((p.2 : Y) * q.2) = ((p.1 : Y) * p.2) * ((q.1 : Y) * q.2)
        have h := hc' _ q.1.2 _ p.2.2
        calc ((p.1 : Y) * q.1) * ((p.2 : Y) * q.2) = (p.1 : Y) * ((q.1 : Y) * p.2) * q.2 := by
              group
          _ = (p.1 : Y) * ((p.2 : Y) * q.1) * q.2 := by rw [h]
          _ = ((p.1 : Y) * p.2) * ((q.1 : Y) * q.2) := by group }
  let π : ↥L × ↥L' →* (↥L ⧸ center ↥L) × (↥L' ⧸ center ↥L') :=
    (QuotientGroup.mk' (center ↥L)).prodMap (QuotientGroup.mk' (center ↥L'))
  have hker : μ.rangeRestrict.ker ≤ π.ker := by
    rintro ⟨x, y⟩ hxy
    have h1 : (x : Y) * y = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hxy)
    have hy : (y : Y) = (x : Y)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hxL' : (x : Y) ∈ L' := by
      have : (x : Y) = (y : Y)⁻¹ := by rw [hy, inv_inv]
      rw [this]
      exact inv_mem y.2
    have hyL : (y : Y) ∈ L := by
      rw [hy]
      exact inv_mem x.2
    have hxZ : x ∈ center ↥L := Subgroup.mem_center_iff.mpr fun l =>
      Subtype.ext (hc' _ l.2 _ hxL')
    have hyZ : y ∈ center ↥L' := Subgroup.mem_center_iff.mpr fun l =>
      Subtype.ext (hc' _ hyL _ l.2).symm
    rw [MonoidHom.mem_ker]
    exact Prod.ext ((QuotientGroup.eq_one_iff _).mpr hxZ) ((QuotientGroup.eq_one_iff _).mpr hyZ)
  let ψ : μ.range →* (↥L ⧸ center ↥L) × (↥L' ⧸ center ↥L') :=
    (MonoidHom.liftOfSurjective μ.rangeRestrict μ.rangeRestrict_surjective) ⟨π, hker⟩
  have hψ : Function.Surjective ψ := by
    intro t
    obtain ⟨p, rfl⟩ := ((QuotientGroup.mk'_surjective _).prodMap
      (QuotientGroup.mk'_surjective _)) t
    exact ⟨μ.rangeRestrict p, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩
  have hY : RankCertified Y 5 := (hc2.of_surjective ψ hψ).of_subgroup
  exact (hY.mono (by norm_num : 4 ≤ 5)).not_sectionalTwoRankLE h4

theorem normal_of_rankCertified_one {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y} {z : Y}
    (hs : Setting125 Y L B X₀ z) (hZ : center ↥L = ⊥) (hc : RankCertified (↥L ⧸ center ↥L) 1)
    (b : Y) : b ∈ normalizer (L : Set Y) := by
  classical
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set L' : Subgroup Y := L.map (MulAut.conj b).toMonoidHom with hL'
  have hL'c : CFSG.IsComponent L' := CFSG.LocalCores.isComponent_map_mulEquiv _ hs.comp
  have hcomm : ⁅L, L'⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hs.comp hL'c with h | h
    · exact absurd h.symm hne
    · exact h
  have hc' : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x := fun x hx y hy => by
    have h1 : ⁅x, y⁆ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  let e : ↥L ≃* ↥L' := L.equivMapOfInjective _ (MulAut.conj b).injective
  have hZ' : center ↥L' = ⊥ := by
    rw [← Subgroup.map_center_eq e, hZ, Subgroup.map_bot]
  have hcL : RankCertified ↥L 1 := hc.of_quotient (center ↥L)
  have hc2 : RankCertified (↥L × ↥L') 3 := hcL.prod (hcL.of_mulEquiv e)
  let μ : ↥L × ↥L' →* Y :=
    { toFun := fun p => (p.1 : Y) * (p.2 : Y)
      map_one' := by simp
      map_mul' := fun p q => by
        change ((p.1 : Y) * q.1) * ((p.2 : Y) * q.2) = ((p.1 : Y) * p.2) * ((q.1 : Y) * q.2)
        have h := hc' _ q.1.2 _ p.2.2
        calc ((p.1 : Y) * q.1) * ((p.2 : Y) * q.2) = (p.1 : Y) * ((q.1 : Y) * p.2) * q.2 := by
              group
          _ = (p.1 : Y) * ((p.2 : Y) * q.1) * q.2 := by rw [h]
          _ = ((p.1 : Y) * p.2) * ((q.1 : Y) * q.2) := by group }
  have hcenL : ∀ x : ↥L, (∀ l : ↥L, (l : Y) * x = x * l) → x = 1 := fun x hx => by
    have : x ∈ center ↥L := Subgroup.mem_center_iff.mpr fun l => Subtype.ext (hx l)
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  have hcenL' : ∀ y : ↥L', (∀ l : ↥L', (l : Y) * y = y * l) → y = 1 := fun y hy => by
    have : y ∈ center ↥L' := Subgroup.mem_center_iff.mpr fun l => Subtype.ext (hy l)
    rw [hZ', Subgroup.mem_bot] at this
    exact this
  have hμ : Function.Injective μ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    rintro ⟨x, y⟩ hxy
    have h1 : (x : Y) * y = 1 := MonoidHom.mem_ker.mp hxy
    have hy : (y : Y) = (x : Y)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hxL' : (x : Y) ∈ L' := by
      have : (x : Y) = (y : Y)⁻¹ := by rw [hy, inv_inv]
      rw [this]
      exact inv_mem y.2
    have hyL : (y : Y) ∈ L := by
      rw [hy]
      exact inv_mem x.2
    have hx1 : x = 1 := hcenL x fun l => hc' _ l.2 _ hxL'
    have hy1 : y = 1 := hcenL' y fun l => (hc' _ hyL _ l.2).symm
    rw [hx1, hy1]
    rfl
  have hM : RankCertified ↥μ.range 3 := hc2.of_mulEquiv (MonoidHom.ofInjective hμ)
  obtain ⟨-, hsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hs.B_el
  have hzM : z ∉ μ.range := by
    rintro ⟨⟨x, y⟩, hxy⟩
    have hzc := Subgroup.mem_center_iff.mp hs.z_cent
    have hz : (x : Y) * y = z := hxy
    have hx1 : x = 1 := hcenL x fun l => by
      have h1 : (l : Y) * ((x : Y) * y) = ((x : Y) * y) * l := by rw [hz]; exact hzc l
      have h2 : (y : Y) * l = l * y := (hc' _ l.2 _ y.2).symm
      calc (l : Y) * x = ((l : Y) * ((x : Y) * y)) * (y : Y)⁻¹ := by group
        _ = (((x : Y) * y) * l) * (y : Y)⁻¹ := by rw [h1]
        _ = (x : Y) * ((y : Y) * l) * (y : Y)⁻¹ := by group
        _ = (x : Y) * (l * y) * (y : Y)⁻¹ := by rw [h2]
        _ = x * l := by group
    have hy1 : y = 1 := hcenL' y fun l => by
      have h1 : (l : Y) * ((x : Y) * y) = ((x : Y) * y) * l := by rw [hz]; exact hzc l
      rw [hx1, Subgroup.coe_one, one_mul] at h1
      exact h1
    apply hs.z_ne
    rw [← hz, hx1, hy1]
    simp
  exact not_rankCertified_three_of_gen4 hs.sec4 (Subgroup.mem_center_iff.mp hs.z_cent)
    (hsq z hs.z_mem) hzM hM

theorem mem_of_rankCertified_three {Y : Type} [Group Y] [Finite Y] {L B X₀ : Subgroup Y} {z : Y}
    (hs : Setting125 Y L B X₀ z) (hc : RankCertified (↥L ⧸ center ↥L) 3) : z ∈ L := by
  by_contra hzL
  obtain ⟨-, hsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hs.B_el
  exact not_rankCertified_three_of_gen4 hs.sec4 (Subgroup.mem_center_iff.mp hs.z_cent)
    (hsq z hs.z_mem) hzL (hc.of_quotient (center ↥L))

end CFSG.GH74.Generic.BProg.B3.S3T2A7
