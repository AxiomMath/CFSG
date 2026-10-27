module

public import CFSG.CGT.PushingUpLit.CGT6.EmbLayer
public import CFSG.CGT.PushingUpLit.CGT6.Diag.Defs
public import CFSG.CGT.PushingUpLit.CGT6.Diag.ReduceCenter

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.LocalCores CFSG.CGT.PushingUpLit.BHS6
open CFSG.CGT.PushingUpLit.CGT6.Diag.Reduce
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

@[expose] def DiagReduction : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb4Cfg G T Y → Out49 G Y → LayerOut G Y →
      (∀ A : Subgroup V, GInv G A → A = ⊥ ∨ A = ⊤) →
      (¬ ∃ K : Subgroup ↥G, CFSG.IsComponent K ∧ Y.subgroupOf G ≤ K) →
        ∃ (K K' : Subgroup (MulAut V)) (t : MulAut V), DiagCfg G T Y K K' t

section Proof

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_involution_of_two_group {T : Subgroup (MulAut V)} (hT1 : T ≠ ⊥)
    (hT2 : IsPGroup 2 ↥T) : ∃ t ∈ T, orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card ↥T := by
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hT1 (Subgroup.eq_bot_of_card_eq T (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 h2
  refine ⟨(t : MulAut V), t.2, ?_⟩
  rw [← ht]
  exact Subgroup.orderOf_coe t

theorem diagReduction_of_schreier (hS : SchreierFor Assembly.InCatalog) (hM4 : SchurMultL2Two) :
    DiagReduction := by
  intro V _ _ hV G T Y cfg h9 hL hirr hno
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hTG : T ≤ G := cfg.adm.hTG
  have hperf : ⁅Y, Y⁆ = Y := cfg.adm.hperf
  have hcls := h9.hcls2
  have hTY : T ≤ Subgroup.centralizer (Y : Set (MulAut V)) := cfg.adm.le_centralizer
  obtain ⟨t, htT, ht2o⟩ := exists_involution_of_two_group cfg.adm.hT1 cfg.adm.hT2
  have htG : t ∈ G := hTG htT
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2o
    omega
  have ht2 : t * t = 1 := by
    have : t ^ 2 = 1 := by rw [← ht2o]; exact pow_orderOf_eq_one t
    rwa [pow_two] at this
  have htC : t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) := ⟨htG, hTY htT⟩
  have hQS : Nine7.QS (Y.subgroupOf G) := qs_subgroupOf hV hYG hperf hcls
  have hYq : CFSG.IsQuasisimple ↥(Y.subgroupOf G) :=
    ⟨⟨hQS.1⟩, hQS.2, Nine7.exists_noncomm_center_quotient hQS⟩
  have hstar : Nine7.Star (Y.subgroupOf G) := star_subgroupOf hYG cfg.cent
  let tx : ↥G := ⟨t, htG⟩
  have htx2 : tx * tx = 1 := Subtype.ext ht2
  have htxo : orderOf tx = 2 := by
    rw [← ht2o]
    exact Subgroup.orderOf_mk t htG
  have hYtx : Y.subgroupOf G ≤ Subgroup.centralizer ({tx} : Set ↥G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff.mp hs]
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hTY htT) (y : MulAut V)
      (Subgroup.mem_subgroupOf.mp hy)).symm
  have hYC : Nine7.IsCompIn (Y.subgroupOf G) (⊤ ⊓ Subgroup.centralizer ({tx} : Set ↥G)) :=
    Nine7.isCompIn_inf_centralizer hQS hstar le_top htxo hYtx
  have hdich : ∀ K : Subgroup ↥G, CFSG.IsComponent K → ⁅Y.subgroupOf G, K⁆ = ⊥ ∨
      Y.subgroupOf G ≤ K ∨ (conjugate K tx ≠ K ∧
        Y.subgroupOf G ≤ ⁅K, Subgroup.zpowers tx⁆) := by
    intro K hK
    have hKc : Nine7.IsCompIn K (⊤ : Subgroup ↥G) :=
      ⟨le_top, hK.2.comap (⊤ : Subgroup ↥G).subtype, ⟨hK.1.1.commutator_eq_top, hK.1.2.1⟩⟩
    have hcat : Assembly.InCatalog (↥K ⧸ Subgroup.center ↥K) :=
      cfg.kgroup K (Subgroup.center ↥K) hK.1.2.1
    exact Nine7.lemma_2_7_two_amb (H := ⊤) (t := tx) (Subgroup.mem_top _) htxo hYC hKc
      (Nine7.glaubermanAt_of_schreier hS hcat)
  have hLG : conjClosure Y G ≤ G := conjClosure_le hYG
  have hLT : layer ↥G ⊔ T.subgroupOf G = ⊤ := by
    rw [hL.layer_eq]
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLG,
      Subgroup.map_subgroupOf_eq_of_le hTG, cfg.gen, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hLY : ∀ N : Subgroup ↥G, (∀ g : ↥G, ∀ y ∈ Y.subgroupOf G, g * y * g⁻¹ ∈ N) →
      layer ↥G ≤ N := by
    intro N hN
    rw [hL.layer_eq]
    have h1 : conjClosure Y G ≤ N.map G.subtype := by
      rw [conjClosure, Subgroup.closure_le]
      rintro _ ⟨g, hg, y, hy, rfl⟩
      exact ⟨⟨g, hg⟩ * ⟨y, hYG hy⟩ * ⟨g, hg⟩⁻¹,
        hN ⟨g, hg⟩ ⟨y, hYG hy⟩ (Subgroup.mem_subgroupOf.mpr hy), by simp⟩
    have h2 := Subgroup.comap_mono (f := G.subtype) h1
    rwa [Subgroup.comap_map_eq_self_of_injective G.subtype_injective] at h2
  have hTYx : T.subgroupOf G ≤
      Subgroup.centralizer ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hTY (Subgroup.mem_subgroupOf.mp hx)) (y : MulAut V)
      (Subgroup.mem_subgroupOf.mp hy)
  obtain ⟨Kx, hKx, hKx', hne, hKK, hYKK, hlay⟩ :=
    exists_swapped_pair hYq hL.y_le htx2 hTYx hLT hLY hdich hno
  set K : Subgroup (MulAut V) := Kx.map G.subtype with hKdef
  have hconj_map : (cj tx Kx).map G.subtype = cj t K := by
    unfold cj
    rw [hKdef, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hKq : CFSG.IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Kx.equivMapOfInjective G.subtype G.subtype_injective) hKx.1
  have hKcomm : ⁅K, cj t K⁆ = ⊥ := by
    have := congrArg (Subgroup.map G.subtype) hKK
    rw [Subgroup.map_commutator, hconj_map, Subgroup.map_bot] at this
    exact this
  have hcomm : ∀ a ∈ K, ∀ b ∈ cj t K, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKcomm ha) b hb).symm
  have hYKK' : Y ≤ K ⊔ cj t K := by
    intro y hy
    have h1 : (⟨y, hYG hy⟩ : ↥G) ∈ Kx ⊔ cj tx Kx := hYKK (Subgroup.mem_subgroupOf.mpr hy)
    have h2 := Subgroup.mem_map_of_mem G.subtype h1
    rw [Subgroup.map_sup, hconj_map] at h2
    exact h2
  have hLeq : conjClosure Y G = K ⊔ cj t K := by
    have h1 := congrArg (Subgroup.map G.subtype) (hL.layer_eq.symm.trans hlay)
    rw [Subgroup.map_subgroupOf_eq_of_le hLG, Subgroup.map_sup, hconj_map] at h1
    exact h1
  have hQSY : Nine7.QS Y := isQuasisimple_of_classX4 hV hperf hcls
  have hYq' : CFSG.IsQuasisimple ↥Y :=
    ⟨⟨hQSY.1⟩, hQSY.2, Nine7.exists_noncomm_center_quotient hQSY⟩
  have hYt : Y ≤ Subgroup.centralizer ({t} : Set (MulAut V)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff.mp hs]
    exact (Subgroup.mem_centralizer_iff.mp (hTY htT) y hy).symm
  have ht2' : t ^ 2 = 1 := by rw [pow_two]; exact ht2
  have hsub := cfg.cent t htC ht1 ht2'
  have hKH : K ⊔ cj t K ≤ G := hLeq ▸ hLG
  have hYmem : ∀ y : MulAut V, y ∈ Y ↔ ∃ k ∈ K, y = k * (t * k * t⁻¹) :=
    diag_eq hKq ht2 hKcomm hYq' hYKK' hYt hKH hsub
  have hoddK : Odd (Nat.card ↥(Subgroup.center ↥K)) := by
    have hL' := hL.oddZ
    have hle : (Subgroup.center ↥K).map K.subtype ≤
        (Subgroup.center ↥(conjClosure Y G)).map (conjClosure Y G).subtype := by
      rintro _ ⟨z, hz, rfl⟩
      have hzL : (z : MulAut V) ∈ conjClosure Y G := by
        rw [hLeq]
        exact Subgroup.mem_sup_left z.2
      refine ⟨⟨z, hzL⟩, ?_, rfl⟩
      show (⟨(z : MulAut V), hzL⟩ : ↥(conjClosure Y G)) ∈ Subgroup.center ↥(conjClosure Y G)
      rw [Subgroup.mem_center_iff]
      intro l
      have hl2 : (l : MulAut V) ∈ K ⊔ cj t K := by
        rw [← hLeq]
        exact l.2
      obtain ⟨a, ha, b, hb, hl⟩ := (Nine7.mem_sup_iff_of_comm hKcomm).1 hl2
      apply Subtype.ext
      have h1 : (z : MulAut V) * a = a * z :=
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨a, ha⟩)).symm
      have h2 : (z : MulAut V) * b = b * z := hcomm z z.2 b hb
      show (l : MulAut V) * z = z * l
      rw [← hl]
      calc a * b * z = a * (b * z) := by group
        _ = a * (z * b) := by rw [← h2]
        _ = (a * z) * b := by group
        _ = (z * a) * b := by rw [h1]
        _ = z * (a * b) := by group
    have h2 : Nat.card ↥(Subgroup.center ↥K) =
        Nat.card ↥((Subgroup.center ↥K).map K.subtype) :=
      (Subgroup.card_map_of_injective K.subtype_injective).symm
    have h3 : Nat.card ↥(Subgroup.center ↥(conjClosure Y G)) =
        Nat.card ↥((Subgroup.center ↥(conjClosure Y G)).map (conjClosure Y G).subtype) :=
      (Subgroup.card_map_of_injective (conjClosure Y G).subtype_injective).symm
    rw [h2]
    rw [h3] at hL'
    exact Odd.of_dvd_nat hL' (Subgroup.card_dvd_of_le hle)
  have hcenterY : Subgroup.center ↥Y = ⊥ := by
    rcases hcls with hX | ⟨n, hn, hΩ⟩
    · rcases emb_four_five_core Y hM4 hV hperf hX with hc | ⟨-, hcard, -, -⟩
      · exact hc
      · exfalso
        have h1 := odd_card_center_diag hKq hcomm hYmem hoddK
        rw [hcard] at h1
        exact absurd h1 (by decide)
    · obtain ⟨-, θ, -⟩ := hΩ
      exact YSL.center_eq_bot ⟨θ⟩
  have hsimpleY : IsSimpleGroup ↥Y := by
    have hs : IsSimpleGroup (↥Y ⧸ Subgroup.center ↥Y) := hQSY.2
    exact ((QuotientGroup.quotientMulEquivOfEq hcenterY).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  refine ⟨K, cj t K, t, ?_⟩
  exact
    { t_sq := ht2
      Kconj := rfl
      comm := hcomm
      quasi := ⟨hKq.1.commutator_eq_top, hKq.2.1⟩
      oddZ := hoddK
      Y_mem := hYmem
      perfY := hperf
      centerY := hcenterY
      simpleY := hsimpleY
      Y_le := hYG
      T_le := hTG
      T_cent := hTY
      t_mem := htT
      cls := hcls
      L_eq := hLeq
      gen := by rw [← hLeq]; exact cfg.gen
      irr := hirr }

end Proof

end CFSG.CGT.PushingUpLit.CGT6
