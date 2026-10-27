module

public import CFSG.GH74.GLS.Stage2.Final.ModelH2Center
public import CFSG.GH74.GLS.Stage2.Final.ModelLayer
public import CFSG.GH74.GLS.Stage2.Final.ModelOneClass
public import CFSG.GH74.GLS.LU.Local.Transport

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

@[expose] def Bsc (M : ModelData F) : Subgroup (Fˣ × Fˣ) where
  carrier := {p | diagGL (sc2 p.1) (sc2 p.2) ∈ M.K4}
  mul_mem' := by
    intro a b ha hb
    show diagGL (sc2 (a.1 * b.1)) (sc2 (a.2 * b.2)) ∈ M.K4
    have : diagGL (sc2 (a.1 * b.1)) (sc2 (a.2 * b.2)) =
        diagGL (sc2 a.1) (sc2 a.2) * diagGL (sc2 b.1) (sc2 b.2) := by
      rw [diagGL_mul, sc2_mul, sc2_mul]
    rw [this]
    exact M.K4.mul_mem ha hb
  one_mem' := by
    show diagGL (sc2 1) (sc2 1) ∈ M.K4
    rw [sc2_one, diagGL_one]
    exact M.K4.one_mem
  inv_mem' := by
    intro a ha
    show diagGL (sc2 a.1⁻¹) (sc2 a.2⁻¹) ∈ M.K4
    have : diagGL (sc2 a.1⁻¹) (sc2 a.2⁻¹) = (diagGL (sc2 a.1) (sc2 a.2))⁻¹ := by
      rw [diagGL_inv, sc2_inv, sc2_inv]
    rw [this]
    exact M.K4.inv_mem ha

@[expose] def bscK (M : ModelData F) : Bsc M →* ↥M.K4 where
  toFun p := ⟨diagGL (sc2 p.1.1) (sc2 p.1.2), p.2⟩
  map_one' := by
    apply Subtype.ext
    show diagGL (sc2 1) (sc2 1) = 1
    rw [sc2_one, diagGL_one]
  map_mul' a b := by
    apply Subtype.ext
    show diagGL (sc2 (a.1.1 * b.1.1)) (sc2 (a.1.2 * b.1.2)) =
      diagGL (sc2 a.1.1) (sc2 a.1.2) * diagGL (sc2 b.1.1) (sc2 b.1.2)
    rw [diagGL_mul, sc2_mul, sc2_mul]

@[expose] def bscP (M : ModelData F) : Bsc M →* PG M := (mkP M).comp (bscK M)

@[expose] def bscRatio (M : ModelData F) : Bsc M →* Fˣ :=
  ((MonoidHom.fst Fˣ Fˣ).comp (Bsc M).subtype) * ((MonoidHom.snd Fˣ Fˣ).comp (Bsc M).subtype)⁻¹

theorem bscRatio_apply (M : ModelData F) (p : Bsc M) : bscRatio M p = p.1.1 * (p.1.2)⁻¹ := rfl

theorem bscP_eq_one_iff (M : ModelData F) (p : Bsc M) : bscP M p = 1 ↔ p.1.1 = p.1.2 := by
  constructor
  · intro h
    have hz : bscK M p ∈ Zs M := (QuotientGroup.eq_one_iff _).1 h
    obtain ⟨c, hc⟩ := mem_Zs.1 hz
    rw [scalar4_eq] at hc
    have h1 : (diagGL (sc2 c) (sc2 c) : GL (Fin 4) F) = diagGL (sc2 p.1.1) (sc2 p.1.2) := hc
    obtain ⟨h2, h3⟩ := diagGL_inj h1
    exact (sc2_inj h2).symm.trans (sc2_inj h3)
  · intro h
    apply (QuotientGroup.eq_one_iff _).2
    refine mem_Zs.2 ⟨p.1.1, ?_⟩
    show (Matrix.GeneralLinearGroup.scalar (Fin 4) p.1.1 : GL (Fin 4) F) =
      diagGL (sc2 p.1.1) (sc2 p.1.2)
    rw [← h]
    exact scalar4_eq _

theorem bscP_ker (M : ModelData F) : (bscP M).ker = (bscRatio M).ker := by
  ext p
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, bscP_eq_one_iff, bscRatio_apply, mul_inv_eq_one]

@[expose] def BSsub (M : ModelData F) : Subgroup (PG M) := (bscP M).range

theorem isCyclic_BSsub [Finite F] (M : ModelData F) : IsCyclic ↥(BSsub M) := by
  have e1 : Bsc M ⧸ (bscP M).ker ≃* ↥(bscP M).range := QuotientGroup.quotientKerEquivRange _
  have e2 : Bsc M ⧸ (bscRatio M).ker ≃* ↥(bscRatio M).range := QuotientGroup.quotientKerEquivRange _
  have e3 : Bsc M ⧸ (bscP M).ker ≃* Bsc M ⧸ (bscRatio M).ker :=
    QuotientGroup.quotientMulEquivOfEq (bscP_ker M)
  have e : ↥(bscP M).range ≃* ↥(bscRatio M).range := e1.symm.trans (e3.trans e2)
  have : IsCyclic ↥(bscRatio M).range := inferInstance
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective


theorem mkP_Phi_mem_E {M : ModelData F} {ρ : CFSG.GH74.Filter.ClassicalOdd.Q8 →* GL (Fin 2) F}
    (hρ : ∀ c, ρ c ∈ M.H2) (c d : CFSG.GH74.Filter.ClassicalOdd.Q8) :
    mkP M (Phi M ρ hρ (c, d)) ∈ K1 M ⊔ K2 M := by
  rw [mem_E_iff]
  refine ⟨⟨ρ c, hρ c⟩, ⟨ρ d, hρ d⟩, ?_⟩
  rw [iota1_apply, iota2_apply, ← map_mul]
  congr 1
  apply Subtype.ext
  show diagGL (ρ c) (ρ d) = blkL F (ρ c) * blkR F (ρ d)
  exact diagGL_eq_blkL_mul_blkR _ _

theorem blockScalar_of_cent_E [Finite F] {M : ModelData F} (hG : GoodModel M) {c : PG M}
    (hc : c ∈ Cg M) (hcomm : ∀ e ∈ K1 M ⊔ K2 M, c * e = e * c) : ∃ p : Bsc M, bscP M p = c := by
  obtain ⟨a, b, hab, hH⟩ := hG.quat
  have hc' : c ∈ (Nsub M).map (mkP M) := by rw [← centralizer_yP]; exact hc
  obtain ⟨n, hn, rfl⟩ := hc'
  obtain ⟨l, m, hlm⟩ := blockScalar_of_comm M hG.two_ne_zero (rhoQ hab) hH
    (rhoQ_irr hab hG.two_ne_zero) (rhoQ_nc hab) hn
    (fun c' d => hcomm _ (mkP_Phi_mem_E hH c' d))
  refine ⟨⟨(l, m), ?_⟩, ?_⟩
  · show diagGL (sc2 l) (sc2 m) ∈ M.K4
    rw [← hlm]
    exact n.2
  · show mkP M ⟨diagGL (sc2 l) (sc2 m), _⟩ = mkP M n
    congr 1
    exact Subtype.ext hlm.symm


theorem mem_of_odd_orderOf_of_index_two {G : Type*} [Group G] (H : Subgroup G) (hH : H.index = 2)
    {x : G} (hx : Odd (orderOf x)) : x ∈ H := by
  have hn : H.Normal := Subgroup.normal_of_index_eq_two hH
  have h1 : orderOf (QuotientGroup.mk x : G ⧸ H) ∣ orderOf x := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]
    rfl
  have h2 : orderOf (QuotientGroup.mk x : G ⧸ H) ∣ 2 := by
    rw [← hH]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk x : G ⧸ H) ∣ Nat.gcd (orderOf x) 2 := Nat.dvd_gcd h1 h2
  have h4 : Nat.gcd (orderOf x) 2 = 1 := by
    rw [Nat.gcd_comm]
    exact Nat.coprime_two_left.2 hx
  rw [h4, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff x).1 h3

theorem pPrimeCoreOf_conj {G : Type*} [Group G] {X : Subgroup G} {c x : G} (hc : c ∈ X)
    (hx : x ∈ pPrimeCoreOf 2 X) : c * x * c⁻¹ ∈ pPrimeCoreOf 2 X := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, (CFSG.pPrimeCore_normal).conj_mem y hy ⟨c, hc⟩, rfl⟩

theorem pPrimeCoreOf_le {G : Type*} [Group G] (X : Subgroup G) : pPrimeCoreOf 2 X ≤ X :=
  Subgroup.map_subtype_le _

theorem odd_card_pPrimeCoreOf {G : Type*} [Group G] [Finite G] (X : Subgroup G) :
    Odd (Nat.card (pPrimeCoreOf 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥X)
  rw [show Nat.card (pPrimeCoreOf 2 X) = Nat.card (pPrimeCore 2 ↥X) from
    (Nat.card_congr (Subgroup.equivMapOfInjective (pPrimeCore 2 ↥X) X.subtype
      X.subtype_injective).toEquiv).symm]
  exact Nat.coprime_two_left.1 h

theorem oddCore_inf_gen [Finite F] {M : ModelData F} (hG : GoodModel M) (ι : ↥M.H2 →* PG M)
    (hinj : Function.Injective ι) (hCg : ∀ a, ι a ∈ Cg M) {a : ↥M.H2}
    (ha : ι a ∈ pPrimeCoreOf 2 (Cg M)) : a = 1 := by
  set Nc := pPrimeCoreOf 2 (Cg M) with hNc
  let N'' : Subgroup ↥M.H2 := Nc.comap ι
  have hnorm : N''.Normal := ⟨fun h hh g => by
    show ι (g * h * g⁻¹) ∈ Nc
    rw [map_mul, map_mul, map_inv]
    exact pPrimeCoreOf_conj (hCg g) hh⟩
  have hodd : Odd (Nat.card N'') := by
    have h1 : Nat.card (N''.map ι) = Nat.card N'' := Subgroup.card_map_of_injective hinj
    have h2 : Nat.card (N''.map ι) ∣ Nat.card Nc :=
      Subgroup.card_dvd_of_le (by rintro _ ⟨x, hx, rfl⟩; exact hx)
    rw [← h1]
    exact Odd.of_dvd_nat (odd_card_pPrimeCoreOf (Cg M)) h2
  have hbot : N'' = ⊥ := ModelGT.normal_odd_eq_bot hG.qs hG.center2 hG.even N'' hodd
  have : a ∈ N'' := ha
  rw [hbot] at this
  exact Subgroup.mem_bot.1 this

theorem oddCore_comm_gen [Finite F] {M : ModelData F} (hG : GoodModel M) (ι : ↥M.H2 →* PG M)
    (hinj : Function.Injective ι) (hCg : ∀ a, ι a ∈ Cg M)
    (hnorm : ∀ c ∈ C0 M, ∀ k ∈ ι.range, c * k * c⁻¹ ∈ ι.range) {x e : PG M}
    (hx : x ∈ pPrimeCoreOf 2 (Cg M)) (he : e ∈ ι.range) : x * e = e * x := by
  have hxC : x ∈ Cg M := pPrimeCoreOf_le _ hx
  have hxC0 : x ∈ C0 M := by
    have hodd : Odd (orderOf x) := by
      have := Subgroup.orderOf_dvd_natCard (pPrimeCoreOf 2 (Cg M)) hx
      exact Odd.of_dvd_nat (odd_card_pPrimeCoreOf (Cg M)) this
    have h2 := mem_of_odd_orderOf_of_index_two ((C0 M).subgroupOf (Cg M)) (index_C0_Cg M hG.two_ne_zero)
      (x := (⟨x, hxC⟩ : ↥(Cg M))) (by rw [Subgroup.orderOf_mk]; exact hodd)
    exact h2
  obtain ⟨b, hb⟩ := hnorm x hxC0 e he
  obtain ⟨a, rfl⟩ := he
  have h1 : ι b * (ι a)⁻¹ ∈ pPrimeCoreOf 2 (Cg M) := by
    rw [hb]
    have h3 : x * ι a * x⁻¹ * (ι a)⁻¹ = x * (ι a * x⁻¹ * (ι a)⁻¹) := by group
    rw [h3]
    exact (pPrimeCoreOf 2 (Cg M)).mul_mem hx
      (pPrimeCoreOf_conj (hCg a) ((pPrimeCoreOf 2 (Cg M)).inv_mem hx))
  have h4 : ι (b * a⁻¹) ∈ pPrimeCoreOf 2 (Cg M) := by rw [map_mul, map_inv]; exact h1
  have h5 : b * a⁻¹ = 1 := oddCore_inf_gen hG ι hinj hCg h4
  have h6 : b = a := mul_inv_eq_one.1 h5
  rw [h6] at hb
  calc x * ι a = (x * ι a * x⁻¹) * x := by group
    _ = ι a * x := by rw [← hb]


theorem pPrimeCoreOf_le_BS [Finite F] {M : ModelData F} (hG : GoodModel M) :
    pPrimeCoreOf 2 (Cg M) ≤ BSsub M := by
  intro x hx
  have h2 := hG.two_ne_zero
  have hxC : x ∈ Cg M := pPrimeCoreOf_le _ hx
  have h1 : ∀ e ∈ K1 M, x * e = e * x := fun e he =>
    oddCore_comm_gen hG (iota1 M) (iota1_injective M) (fun a => K1_le_Cg M ⟨a, rfl⟩)
      (fun c hc k hk => C0_conj_K1 M h2 hc hk) hx he
  have h2' : ∀ e ∈ K2 M, x * e = e * x := fun e he =>
    oddCore_comm_gen hG (iota2 M) (iota2_injective M) (fun a => K2_le_Cg M ⟨a, rfl⟩)
      (fun c hc k hk => C0_conj_K2 M h2 hc hk) hx he
  have hle : K1 M ⊔ K2 M ≤ Subgroup.centralizer {x} :=
    sup_le (fun e he => Subgroup.mem_centralizer_singleton_iff.2 (h1 e he).symm)
      (fun e he => Subgroup.mem_centralizer_singleton_iff.2 (h2' e he).symm)
  obtain ⟨p, hp⟩ := blockScalar_of_cent_E hG hxC (fun e he =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hle he)).symm)
  exact ⟨p, hp⟩

theorem isCyclic_pPrimeCoreOf [Finite F] {M : ModelData F} (hG : GoodModel M) :
    IsCyclic ↥(pPrimeCoreOf 2 (Cg M)) := by
  have hle : pPrimeCoreOf 2 (Cg M) ≤ BSsub M := pPrimeCoreOf_le_BS hG
  have : IsCyclic ↥(BSsub M) := isCyclic_BSsub M
  have e := Subgroup.subgroupOfEquivOfLe hle
  have : IsCyclic ↥((pPrimeCoreOf 2 (Cg M)).subgroupOf (BSsub M)) := Subgroup.isCyclic _
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem isCompIn_K1 [Finite F] {M : ModelData F} (hG : GoodModel M) :
    CFSG.GH74.GLS.IsCompIn (Cg M) (K1 M) := by
  have h2 := hG.two_ne_zero
  have hC0n : ((C0 M).subgroupOf (Cg M)).Normal :=
    Subgroup.normal_of_index_eq_two (index_C0_Cg M h2)
  have hn1 : ((K1 M).subgroupOf (C0 M)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact C0_conj_K1 M h2 g.2 hx
  exact ⟨K1_le_Cg M, ModelGT.isComponent_subgroupOf (quasisimple_K1 M hG.qs) (K1_le_C0 M)
    (C0_le_Cg M) hn1 hC0n⟩

theorem isCompIn_K2 [Finite F] {M : ModelData F} (hG : GoodModel M) :
    CFSG.GH74.GLS.IsCompIn (Cg M) (K2 M) := by
  have h2 := hG.two_ne_zero
  have hC0n : ((C0 M).subgroupOf (Cg M)).Normal :=
    Subgroup.normal_of_index_eq_two (index_C0_Cg M h2)
  have hn2 : ((K2 M).subgroupOf (C0 M)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact C0_conj_K2 M h2 g.2 hx
  exact ⟨K2_le_Cg M, ModelGT.isComponent_subgroupOf (quasisimple_K2 M hG.qs) (K2_le_C0 M)
    (C0_le_Cg M) hn2 hC0n⟩


theorem only_comps [Finite F] {M : ModelData F} (hG : GoodModel M) {L : Subgroup (PG M)}
    (hL : CFSG.GH74.GLS.IsPCompIn 2 (Cg M) L) : L = K1 M ∨ L = K2 M := by
  have hcomp := CFSG.GH74.GLS.LU.Local.isCompIn_of_isPCompIn_two (isCyclic_pPrimeCoreOf hG) hL
  have hK1 := isCompIn_K1 hG
  have hK2 := isCompIn_K2 hG
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hn1, hn2⟩ := hne
  have hsub : ∀ {A : Subgroup (PG M)}, A ≤ Cg M → A ≠ L →
      A.subgroupOf (Cg M) ≠ L.subgroupOf (Cg M) := fun {A} hA hAL h => by
    apply hAL
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_eq_left.2 hA, inf_eq_left.2 hcomp.1] at this
  have hcomm : ∀ {A : Subgroup (PG M)}, CFSG.GH74.GLS.IsCompIn (Cg M) A → A ≠ L →
      ∀ l ∈ L, ∀ e ∈ A, l * e = e * l := by
    intro A hA hAL l hl e he
    rcases CFSG.LocalCores.distinct_components_commute hcomp.2 hA.2 with h | h
    · exact absurd h.symm (hsub hA.1 hAL)
    · have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
      have hl' : (⟨l, hcomp.1 hl⟩ : ↥(Cg M)) ∈ L.subgroupOf (Cg M) := hl
      have he' : (⟨e, hA.1 he⟩ : ↥(Cg M)) ∈ A.subgroupOf (Cg M) := he
      have := Subgroup.mem_centralizer_iff.1 (hle hl') ⟨e, hA.1 he⟩ he'
      exact (congrArg Subtype.val this).symm
  have hBS : ∀ l ∈ L, l ∈ BSsub M := by
    intro l hl
    have hle : K1 M ⊔ K2 M ≤ Subgroup.centralizer {l} :=
      sup_le (fun e he => Subgroup.mem_centralizer_singleton_iff.2
          (hcomm hK1 (fun h => hn1 h.symm) l hl e he).symm)
        (fun e he => Subgroup.mem_centralizer_singleton_iff.2
          (hcomm hK2 (fun h => hn2 h.symm) l hl e he).symm)
    obtain ⟨p, hp⟩ := blockScalar_of_cent_E hG (hcomp.1 hl) (fun e he =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hle he)).symm)
    exact ⟨p, hp⟩
  have hcyc : IsCyclic ↥(BSsub M) := isCyclic_BSsub M
  have hab : ∀ l ∈ L, ∀ l' ∈ L, l * l' = l' * l := by
    intro l hl l' hl'
    let _inst : CommGroup ↥(BSsub M) := IsCyclic.commGroup
    have := mul_comm (⟨l, hBS l hl⟩ : ↥(BSsub M)) ⟨l', hBS l' hl'⟩
    exact congrArg Subtype.val this
  have hcentral : L.subgroupOf (Cg M) ≤ Subgroup.centralizer ((L.subgroupOf (Cg M) : Subgroup ↥(Cg M)) : Set ↥(Cg M)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subtype.ext (hab b hb a ha)
  have hcb : ⁅L.subgroupOf (Cg M), L.subgroupOf (Cg M)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcentral
  have hperf := Subgroup.isPerfect_iff.1 hcomp.2.1.1
  rw [hcb] at hperf
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hcomp.2.1
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥(L.subgroupOf (Cg M)))
  apply hx
  have hxm : (x : ↥(Cg M)) ∈ (⊥ : Subgroup ↥(Cg M)) := by
    rw [hperf]
    exact x.2
  exact Subtype.ext (Subgroup.mem_bot.1 hxm)


theorem iota1_eq_iota2_scalar {M : ModelData F} (a b : ↥M.H2) (h : iota1 M a = iota2 M b) :
    ∃ l : Fˣ, (a : GL (Fin 2) F) = sc2 l := by
  rw [iota1_apply, iota2_apply] at h
  obtain ⟨c, hc⟩ := mkP_eq_iff.1 h
  have h1 : (diagGL (a : GL (Fin 2) F) 1)⁻¹ * diagGL 1 (b : GL (Fin 2) F) =
      diagGL (sc2 c) (sc2 c) := by
    rw [← scalar4_eq]
    exact hc
  rw [diagGL_inv, diagGL_mul, inv_one, mul_one, one_mul] at h1
  obtain ⟨h2, -⟩ := diagGL_inj h1
  refine ⟨c⁻¹, ?_⟩
  have h3 := inv_eq_iff_eq_inv.1 h2
  rw [← sc2_inv]
  exact h3

theorem K1_ne_K2 [Finite F] {M : ModelData F} (hG : GoodModel M) : K1 M ≠ K2 M := by
  obtain ⟨a, b, hab, hH⟩ := hG.quat
  obtain ⟨c₀, hc₀⟩ := rhoQ_nc hab
  intro h
  have h1 : iota1 M ⟨rhoQ hab c₀, hH c₀⟩ ∈ K2 M := h ▸ ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ := h1
  obtain ⟨l, hl⟩ := iota1_eq_iota2_scalar _ _ hb'.symm
  exact hc₀ l hl

theorem center_H2_eq' [Finite F] {M : ModelData F} (hG : GoodModel M) :
    Subgroup.center ↥M.H2 = Subgroup.zpowers (⟨-1, M.neg_one_mem_H2⟩ : ↥M.H2) := by
  apply Subgroup.map_injective M.H2.subtype_injective
  rw [center_H2_eq hG, MonoidHom.map_zpowers]
  rfl

theorem cen_range [Finite F] {M : ModelData F} (hG : GoodModel M) (ι : ↥M.H2 →* PG M)
    (hinj : Function.Injective ι) (hι : ι ⟨-1, M.neg_one_mem_H2⟩ = yP M) :
    (Subgroup.center ↥ι.range).map ι.range.subtype = Subgroup.zpowers (yP M) := by
  apply le_antisymm
  · rintro _ ⟨k, hk, rfl⟩
    obtain ⟨_, ⟨a, rfl⟩⟩ := k
    have hac : a ∈ Subgroup.center ↥M.H2 := by
      rw [Subgroup.mem_center_iff]
      intro h
      have := Subgroup.mem_center_iff.1 hk ⟨ι h, h, rfl⟩
      have h1 : ι h * ι a = ι a * ι h := congrArg Subtype.val this
      apply hinj
      rw [map_mul, map_mul]
      exact h1
    rw [center_H2_eq' hG] at hac
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hac
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    show yP M ^ n = ι a
    rw [← hn, map_zpow, hι]
  · rw [Subgroup.zpowers_le]
    refine ⟨⟨yP M, MonoidHom.mem_range.2 ⟨⟨-1, M.neg_one_mem_H2⟩, hι⟩⟩,
      Subgroup.mem_center_iff.2 ?_, rfl⟩
    rintro ⟨_, hk⟩
    obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hk
    apply Subtype.ext
    show ι h * yP M = yP M * ι h
    have hc : (⟨-1, M.neg_one_mem_H2⟩ : ↥M.H2) ∈ Subgroup.center ↥M.H2 := by
      rw [center_H2_eq' hG]
      exact Subgroup.mem_zpowers _
    rw [← hι, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hc h)]

theorem iota1_negOne (M : ModelData F) : iota1 M ⟨-1, M.neg_one_mem_H2⟩ = yP M := rfl

theorem iota2_negOne (M : ModelData F) : iota2 M ⟨-1, M.neg_one_mem_H2⟩ = yP M :=
  mkP_xyK M

theorem hasSL2Model_range {G H : Type} [Group G] [Group H] (ι : H →* G)
    (hinj : Function.Injective ι) {P : ℕ → Prop} (h : CFSG.GH74.GLS.HasSL2Model H P) :
    CFSG.GH74.GLS.HasSL2Model ↥ι.range P := by
  obtain ⟨F', iF, fF, hP, ⟨e⟩⟩ := h
  exact ⟨F', iF, fF, hP, ⟨(MonoidHom.ofInjective hinj).symm.trans e⟩⟩

theorem luComps_PG [Finite F] {M : ModelData F} (hG : GoodModel M) (q : ℕ)
    (hSL : CFSG.GH74.GLS.HasSL2Model ↥M.H2 (fun r => r = q)) :
    CFSG.GH74.GLS.LU.Local.LUComps (PG M) q (yP M) (K1 M) (K2 M) where
  comp₁ := isCompIn_K1 hG
  comp₂ := isCompIn_K2 hG
  ne := K1_ne_K2 hG
  only _ hL := only_comps hG hL
  sl₁ := hasSL2Model_range (iota1 M) (iota1_injective M) hSL
  sl₂ := hasSL2Model_range (iota2 M) (iota2_injective M) hSL
  cen₁ := cen_range hG (iota1 M) (iota1_injective M) (iota1_negOne M)
  cen₂ := cen_range hG (iota2 M) (iota2_injective M) (iota2_negOne M)

end CFSG.GH74.GLS.Stage2.Final.ModelBlock

