module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3316J
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3316P
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316R

public section
namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)

namespace L3316

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem sp4_levi_data_F4 {T M L D : Subgroup G} (h : Hyp331 G T M L D) (h14 : Stmt3_3_14_F4)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) {α : ↥L →* ↥(StatedSp 2 F)}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L)
    (hmapU : ((T ⊓ L).subgroupOf L).map α = unipotent 2 F) (j : Fin 2)
    (hTP : T ≤ Subgroup.normalizer (liftPre α (Q2 F j) : Set G))
    (hinn : InducesInnerOn T (liftCore α (Q2 F j))) :
    (∀ t ∈ T, ∃ lt : ↥L, (lt : G) ∈ T ∧ ∀ (l : ↥L) (hm : t * (l : G) * t⁻¹ ∈ L),
      α ⟨t * l * t⁻¹, hm⟩ = α lt * α l * (α lt)⁻¹) ∧
    ∃ x : ↥L, orderOf x = 3 ∧ (∃ l : Fˣ, l ≠ 1 ∧ α x = Sp4Aut.torSp j l) ∧
      (x : G) ∈ Subgroup.normalizer (T : Set G) ∧
      ∀ y ∈ liftCore α (Q2 F j),
        (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ pCoreOf 2 (liftCore α (Q2 F j)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := liftCore α (Q2 F j) with hYdef
  obtain ⟨-, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  have hFn : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]
  have hF4 : ∃ s : Finset F, s.card = 4 := ⟨Finset.univ, by rw [Finset.card_univ, hF]⟩
  have hF4' : 4 ≤ Nat.card F := hFn.ge
  have : CharP F 2 := SzN15.charP_two_of_card (m := 2) (by rw [hFn]; norm_num)
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := fun t ht =>
    mem_normalizer_perfectCore (hTP ht)
  have hYL : Y ≤ L := liftCore_le α (Q2 F j)
  have hS₀ : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal h.toSetup331.isSylowTwoOf le_sup_left
      (sup_le Subgroup.le_normalizer hTL)
  have hPT : pCoreOf 2 L ≤ T := (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS₀).trans inf_le_left
  have hαY : ∀ y : ↥L, (y : G) ∈ Y → α y ∈ perfectCore (Q2 F j) := by
    intro y hy
    rw [hYdef, liftCore_eq] at hy
    obtain ⟨l, hl, hly⟩ := hy
    have : l = y := Subtype.ext hly
    rw [← this, ← map_perfectCore_comap hα]
    exact ⟨l, hl, rfl⟩
  have hαYs : ∀ z ∈ perfectCore (Q2 F j), ∃ y : ↥L, (y : G) ∈ Y ∧ α y = z := by
    intro z hz
    rw [← map_perfectCore_comap hα] at hz
    obtain ⟨l, hl, rfl⟩ := hz
    refine ⟨l, ?_, rfl⟩
    rw [hYdef, liftCore_eq]
    exact ⟨l, hl, rfl⟩
  let αY : ↥Y →* ↥(perfectCore (Q2 F j)) :=
    (α.comp (Subgroup.inclusion hYL)).codRestrict _ (fun y => hαY _ y.2)
  have hαYv : ∀ y : ↥Y, ((αY y : ↥(perfectCore (Q2 F j))) : StatedSp 2 F) =
      α ⟨y, hYL y.2⟩ := fun y => rfl
  have hαYsurj : Function.Surjective αY := by
    rintro ⟨z, hz⟩
    obtain ⟨y, hyY, rfl⟩ := hαYs z hz
    exact ⟨⟨y, hyY⟩, rfl⟩
  let g : ↥Y →* Matrix.SpecialLinearGroup (Fin 2) F := (blkN j).comp αY
  have hgs : Function.Surjective g := (blkN_surjective hF4 j).comp hαYsurj
  have hgO : ∀ o : ↥Y, (o : G) ∈ pCoreOf 2 Y → g o = 1 := by
    have hsimp : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup hF4'
    have hW : (CFSG.pCore 2 ↥Y).map g = ⊥ := by
      have : ((CFSG.pCore 2 ↥Y).map g).Normal := (CFSG.pCore_normal (p := 2) (G := ↥Y)).map g hgs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥Y).map g) with h1 | h1
      · exact h1
      · exfalso
        have hp : IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) F) := by
          have h2 := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map g
          rw [h1] at h2
          exact h2.of_equiv Subgroup.topEquiv
        have := hp.isNilpotent
        exact CFSG.Quasithin.SL2Sylow.not_isSolvable_sl2 hF4' inferInstance
    intro o ho
    rw [pCoreOf] at ho
    obtain ⟨o', ho', hoo⟩ := ho
    have : o' = o := Subtype.ext hoo
    subst this
    have h1 : g o' ∈ (CFSG.pCore 2 ↥Y).map g := ⟨o', ho', rfl⟩
    rw [hW] at h1
    exact h1
  have hgk : ∀ w : ↥Y, g w = 1 → (w : G) ∈ pCoreOf 2 Y := by
    have hk2 : IsPGroup 2 ↥g.ker := by
      rintro ⟨w, hw⟩
      have hw' : αY w ∈ (blkN j).ker := MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hw)
      obtain ⟨a, ha⟩ := blkN_ker_isPGroup ⟨2, by rw [hFn]; norm_num⟩ j ⟨αY w, hw'⟩
      have ha' : α ⟨((w ^ 2 ^ a : ↥Y) : G), hYL (w ^ 2 ^ a).2⟩ = 1 := by
        have : αY (w ^ 2 ^ a) = 1 := by
          rw [map_pow]
          exact congrArg Subtype.val ha
        exact congrArg Subtype.val this
      have hmem : (⟨((w ^ 2 ^ a : ↥Y) : G), hYL (w ^ 2 ^ a).2⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
        rw [← hker]
        exact ha'
      obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hmem⟩
      refine ⟨a + b, Subtype.ext (Subtype.ext ?_)⟩
      have hb' := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hb
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hb' ⊢
      rw [pow_add, pow_mul]
      exact hb'
    intro w hw
    exact mem_pCoreOf_of_ker_isPGroup hk2 hw
  have hinner : ∀ t (ht : t ∈ T), ∃ gt : StatedSp 2 F, ∀ l : ↥L,
      α ⟨t * l * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp l.2⟩ = gt * α l * gt⁻¹ := by
    intro t ht
    obtain ⟨φ, hφ⟩ := exists_inducedAut hα hker (hTL ht)
    have hQle : (Q2 F j).map φ.toMonoidHom ≤ Q2 F j := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨l', rfl⟩ := hα q
      show φ (α l') ∈ Q2 F j
      rw [hφ]
      have h1 : (l' : G) ∈ liftPre α (Q2 F j) := ⟨l', hq, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp (hTP ht) _).mp h1
      obtain ⟨l'', hl'', hl''e⟩ := h2
      have : l'' = ⟨t * l' * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTL ht) l').mp l'.2⟩ :=
        Subtype.ext hl''e
      rw [← this]
      exact hl''
    have hQ : (Q2 F j).map φ.toMonoidHom = Q2 F j := by
      refine Subgroup.eq_of_le_of_card_ge hQle ?_
      rw [Subgroup.card_map_of_injective φ.injective]
    obtain ⟨y₀, hy₀, hy₀c⟩ := hinn t ht
    have hlevi : ∀ (x : ↥(perfectCore (Q2 F j))) (hx : φ x ∈ perfectCore (Q2 F j)),
        blkN j ⟨φ x, hx⟩ = g ⟨y₀, hy₀⟩ * blkN j x * (g ⟨y₀, hy₀⟩)⁻¹ := by
      intro x hx
      obtain ⟨xl, hxY, hxe⟩ := hαYs x x.2
      have htx : t * (xl : G) * t⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hTY ht) _).mp hxY
      have hyx : y₀ * (xl : G) * y₀⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hy₀ hxY) (Y.inv_mem hy₀)
      have h1 := hgO (⟨t * xl * t⁻¹, htx⟩ * (⟨y₀ * xl * y₀⁻¹, hyx⟩)⁻¹) (hy₀c xl hxY)
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      have h2 : (⟨φ x, hx⟩ : ↥(perfectCore (Q2 F j))) = αY ⟨t * xl * t⁻¹, htx⟩ := by
        apply Subtype.ext
        rw [hαYv]
        show φ (x : StatedSp 2 F) = _
        rw [← hxe, hφ]
      have h3 : x = αY ⟨xl, hxY⟩ := Subtype.ext (by rw [hαYv]; exact hxe.symm)
      have h4 : (⟨y₀ * xl * y₀⁻¹, hyx⟩ : ↥Y) = ⟨y₀, hy₀⟩ * ⟨xl, hxY⟩ * (⟨y₀, hy₀⟩)⁻¹ := rfl
      rw [h2, h3]
      show g ⟨t * xl * t⁻¹, htx⟩ = _
      rw [h1, h4, map_mul, map_mul, map_inv]
      rfl
    obtain ⟨gt, hgt⟩ := Sp4Aut.inner_of_levi hF4 φ j hQ (g ⟨y₀, hy₀⟩) hlevi
    exact ⟨gt, fun l => by rw [← hφ, hgt]⟩
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  have hcen : Subgroup.center ↥(StatedSp 2 F) = ⊥ :=
    CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num)
  have hUL : ∀ u ∈ unipotent 2 F, ∃ l : ↥L, (l : G) ∈ T ∧ α l = u := by
    intro u hu
    rw [← hmapU] at hu
    obtain ⟨l, hl, rfl⟩ := hu
    exact ⟨l, (Subgroup.mem_subgroupOf.mp hl).1, rfl⟩
  have hLU : ∀ l : ↥L, (l : G) ∈ T → α l ∈ unipotent 2 F := by
    intro l hl
    rw [← hmapU]
    exact ⟨l, Subgroup.mem_subgroupOf.mpr ⟨hl, l.2⟩, rfl⟩
  have hTin : ∀ t ∈ T, ∃ lt : ↥L, (lt : G) ∈ T ∧ ∀ (l : ↥L) (hm : t * (l : G) * t⁻¹ ∈ L),
      α ⟨t * l * t⁻¹, hm⟩ = α lt * α l * (α lt)⁻¹ := by
    intro t ht
    obtain ⟨gt, hgt⟩ := hinner t ht
    have hgU : ∀ u ∈ unipotent 2 F, gt * u * gt⁻¹ ∈ unipotent 2 F := by
      intro u hu
      obtain ⟨l, hlT, rfl⟩ := hUL u hu
      rw [← hgt l]
      exact hLU _ (T.mul_mem (T.mul_mem ht hlT) (T.inv_mem ht))
    obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
    have htk : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hpow : ∀ (n : ℕ) (l : ↥L) (hm : t ^ n * (l : G) * (t ^ n)⁻¹ ∈ L),
        α ⟨t ^ n * l * (t ^ n)⁻¹, hm⟩ = gt ^ n * α l * (gt ^ n)⁻¹ := by
      intro n
      induction n with
      | zero =>
        intro l hm
        simp only [pow_zero, one_mul, inv_one, mul_one]
      | succ n ih =>
        intro l hm
        have hm' : t ^ n * (l : G) * (t ^ n)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (pow_mem (hTL ht) n) l).mp l.2
        have h1 : (⟨t ^ (n + 1) * l * (t ^ (n + 1))⁻¹, hm⟩ : ↥L) =
            ⟨t * ((⟨t ^ n * l * (t ^ n)⁻¹, hm'⟩ : ↥L) : G) * t⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hTL ht) _).mp hm'⟩ := by
          apply Subtype.ext
          simp only [pow_succ']
          group
        rw [h1, hgt, ih l hm', pow_succ']
        group
    have hgk2 : gt ^ 2 ^ k = 1 := by
      have hc : gt ^ 2 ^ k ∈ Subgroup.center ↥(StatedSp 2 F) := by
        rw [Subgroup.mem_center_iff]
        intro z
        obtain ⟨l, rfl⟩ := hα z
        have hm : t ^ 2 ^ k * (l : G) * (t ^ 2 ^ k)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (pow_mem (hTL ht) _) l).mp l.2
        have h1 := hpow (2 ^ k) l hm
        have h2 : (⟨t ^ 2 ^ k * l * (t ^ 2 ^ k)⁻¹, hm⟩ : ↥L) = l :=
          Subtype.ext (by simp [htk])
        rw [h2] at h1
        calc α l * gt ^ 2 ^ k = (gt ^ 2 ^ k * α l * (gt ^ 2 ^ k)⁻¹) * gt ^ 2 ^ k := by
              rw [← h1]
          _ = gt ^ 2 ^ k * α l := by group
      rw [hcen] at hc
      exact hc
    have hgtU : gt ∈ unipotent 2 F := mem_unipotent_of_normalizes hgU hgk2
    obtain ⟨lt, hltT, hlt⟩ := hUL gt hgtU
    refine ⟨lt, hltT, fun l hm => ?_⟩
    rw [hlt]
    exact hgt l
  obtain ⟨x₀, hx₀3, lam, hlam1, hx₀⟩ := exists_torus_lift hF hα hker j
  refine ⟨hTin, x₀, hx₀3, ⟨lam, hlam1, hx₀⟩, ?_, ?_⟩
  ·
    apply mem_normalizer_of_map_le
    rintro _ ⟨t, ht, rfl⟩
    show (x₀ : G) * t * (x₀ : G)⁻¹ ∈ T
    obtain ⟨lt, hltT, hlt⟩ := hTin t ht
    set c : G := (lt : G)⁻¹ * t with hc
    have hcT : c ∈ T := T.mul_mem (T.inv_mem hltT) ht
    have hcx : c * x₀ * c⁻¹ * (x₀ : G)⁻¹ ∈ T := by
      have hm : t * (x₀ : G) * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hTL ht) x₀).mp x₀.2
      have h1 := hlt x₀ hm
      have h2 : α (lt⁻¹ * ⟨t * x₀ * t⁻¹, hm⟩ * lt * x₀⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      have h3 := hPT (mem_pCoreOf_of_ker hker h2)
      convert h3 using 1
      simp only [hc, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hxl : (x₀ : G) * lt * (x₀ : G)⁻¹ ∈ T := by
      have h1 : α (x₀ * lt * x₀⁻¹) ∈ unipotent 2 F := by
        rw [map_mul, map_mul, map_inv, hx₀]
        exact (Subgroup.mem_normalizer_iff.mp (Sp4Aut.torSp_mem_normalizer j lam) _).mp
          (hLU lt hltT)
      obtain ⟨l'', hl''T, hl''⟩ := hUL _ h1
      have h2 : α (l''⁻¹ * (x₀ * lt * x₀⁻¹)) = 1 := by
        rw [map_mul, map_inv, hl'', inv_mul_cancel]
      have h3 := hPT (mem_pCoreOf_of_ker hker h2)
      have h4 := T.mul_mem hl''T h3
      simpa using h4
    have h := T.mul_mem (T.mul_mem hxl (T.inv_mem hcx)) hcT
    convert h using 1
    simp only [hc]
    group
  ·
    intro y hy
    have hxQ : α x₀ ∈ Q2 F j := by
      rw [hx₀]
      exact Sp4Aut.torSp_mem_Q2 j lam
    have hxP : (x₀ : G) ∈ Subgroup.normalizer (liftPre α (Q2 F j) : Set G) := by
      apply mem_normalizer_of_map_le
      rintro _ ⟨p, ⟨lp, hlp, rfl⟩, rfl⟩
      refine ⟨x₀ * lp * x₀⁻¹, ?_, rfl⟩
      show α (x₀ * lp * x₀⁻¹) ∈ Q2 F j
      rw [map_mul, map_mul, map_inv]
      exact (Q2 F j).mul_mem ((Q2 F j).mul_mem hxQ hlp) ((Q2 F j).inv_mem hxQ)
    have hxY : (x₀ : G) ∈ Subgroup.normalizer (Y : Set G) := mem_normalizer_perfectCore hxP
    have hw : (x₀ : G) * y * (x₀ : G)⁻¹ * y⁻¹ ∈ Y :=
      Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hxY y).mp hy) (Y.inv_mem hy)
    refine hgk ⟨_, hw⟩ ?_
    have hyL := hYL hy
    have hyQ : α ⟨y, hyL⟩ ∈ Q2 F j := perfectCore_le _ (hαY _ hy)
    apply Subtype.ext
    show blkQ j (Subgroup.inclusion (perfectCore_le (Q2 F j)) (αY ⟨_, hw⟩)) = 1
    have heq : Subgroup.inclusion (perfectCore_le (Q2 F j)) (αY ⟨_, hw⟩) =
        ⟨α x₀, hxQ⟩ * ⟨α ⟨y, hyL⟩, hyQ⟩ * (⟨α x₀, hxQ⟩)⁻¹ * (⟨α ⟨y, hyL⟩, hyQ⟩)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion, hαYv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact congrArg α (Subtype.ext rfl)
    rw [heq]
    refine Sp4Aut.blkQ_commutator (Or.inl ?_)
    have h1 : (⟨α x₀, hxQ⟩ : ↥(Q2 F j)) = ⟨Sp4Aut.torSp j lam, Sp4Aut.torSp_mem_Q2 j lam⟩ :=
      Subtype.ext hx₀
    rw [h1]
    exact Sp4Aut.blkQ_torSp j lam

theorem sp4_endgame_F4 {T M L D : Subgroup G}
    (h : Hyp331 G T M L D) (h14 : Stmt3_3_14_F4) (hJ1 : FactJ1Norm3312)
    (hGA : GriessAllModelsStatement) (hZ : FactSp4BlockZ) (hb : IsSp4Block L) {F : Type}
    [Field F] [Fintype F] (hF : Fintype.card F = 4) {α : ↥L →* ↥(StatedSp 2 F)}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L)
    (hmapU : ((T ⊓ L).subgroupOf L).map α = unipotent 2 F) (j : Fin 2)
    (hTP : T ≤ Subgroup.normalizer (liftPre α (Q2 F j) : Set G))
    (hY : liftCore α (Q2 F j) ∈ lFamilyOf L T) (hinn : InducesInnerOn T (liftCore α (Q2 F j)))
    (hO : pCoreOf 2 (liftCore α (Q2 F j) ⊔ T ⊔ D) ≠ ⊥) {Kc : Subgroup G}
    (hKc : Kc ∈ cComp (liftCore α (Q2 F j) ⊔ T ⊔ D)) (hYK : liftCore α (Q2 F j) ≤ Kc)
    (hHK : liftCore α (Q2 F j) ⊔ T ⊔ D ≤ Subgroup.normalizer (Kc : Set G))
    (hc : A312C15 (modO2Image (liftCore α (Q2 F j) ⊔ T ⊔ D) (liftCore α (Q2 F j)))
      (modO2Image (liftCore α (Q2 F j) ⊔ T ⊔ D) Kc)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := liftCore α (Q2 F j) with hYdef
  obtain ⟨-, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  have hFn : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]
  have hF4 : ∃ s : Finset F, s.card = 4 := ⟨Finset.univ, by rw [Finset.card_univ, hF]⟩
  have : CharP F 2 := SzN15.charP_two_of_card (m := 2) (by rw [hFn]; norm_num)
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := fun t ht =>
    mem_normalizer_perfectCore (hTP ht)
  obtain ⟨hTin, x₀, hx₀3, ⟨lam, hlam1, hx₀⟩, hxT, hxy⟩ :=
    sp4_levi_data_F4 h h14 hF hα hker hmapU j hTP hinn
  set x : G := (x₀ : G) with hxdef
  have hx3 : orderOf x = 3 := by rw [hxdef, Subgroup.orderOf_coe, hx₀3]
  obtain ⟨hKQ, hQT, -⟩ := j1_step h hJ1 hY hTY hO hKc hYK hHK hc hx3 x₀.2 hxT hxy
  set Q := ⁅T, Subgroup.zpowers x⁆ with hQdef
  have hQ2 : IsPGroup 2 ↥Q := h.sylow.1.to_le hQT
  have hUL : ∀ u ∈ unipotent 2 F, ∃ l : ↥L, (l : G) ∈ T ∧ α l = u := by
    intro u hu
    rw [← hmapU] at hu
    obtain ⟨l, hl, rfl⟩ := hu
    exact ⟨l, (Subgroup.mem_subgroupOf.mp hl).1, rfl⟩
  have hLU : ∀ l : ↥L, (l : G) ∈ T → α l ∈ unipotent 2 F := by
    intro l hl
    rw [← hmapU]
    exact ⟨l, Subgroup.mem_subgroupOf.mpr ⟨hl, l.2⟩, rfl⟩
  have hQR : Q ≤ ((Sp4Aut.radSp F j).comap α).map L.subtype := by
    rw [hQdef, Subgroup.commutator_le]
    intro t ht x' hx'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
    obtain ⟨lt, hltT, hlt⟩ := hTin t ht
    have hxm : x ^ m = ((x₀ ^ m : ↥L) : G) := by rw [hxdef, Subgroup.coe_zpow]
    have hm : t * ((x₀ ^ m : ↥L) : G) * t⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hTL ht) _).mp (x₀ ^ m).2
    refine ⟨⟨t * ((x₀ ^ m : ↥L) : G) * t⁻¹, hm⟩ * (x₀ ^ m)⁻¹, ?_, ?_⟩
    · show α (⟨t * ((x₀ ^ m : ↥L) : G) * t⁻¹, hm⟩ * (x₀ ^ m)⁻¹) ∈ Sp4Aut.radSp F j
      rw [map_mul, hlt, map_inv, map_zpow, hx₀, ← map_zpow]
      exact Sp4Aut.commutator_mem_radSp (hLU lt hltT) (lam ^ m)
    · rw [commutatorElement_def, hxm]
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  have hcardQ : Nat.card ↥Q ≤ 2 ^ 17 := by
    have h1 : Nat.card ↥Q ≤ Nat.card ↥(((Sp4Aut.radSp F j).comap α).map L.subtype) :=
      Subgroup.card_le_of_le hQR
    rw [Subgroup.card_map_of_injective L.subtype_injective, card_comap_of_surjective hα,
      hker] at h1
    have h2 : Nat.card ↥(CFSG.pCore 2 ↥L) = Nat.card ↥(pCoreOf 2 L) := by
      rw [pCoreOf, Subgroup.card_map_of_injective L.subtype_injective]
    rw [h2] at h1
    calc Nat.card ↥Q ≤ _ := h1
      _ ≤ 2 ^ 10 * 2 ^ 7 :=
        Nat.mul_le_mul (card_pCoreOf_le hGA hZ hb) (Sp4Aut.card_radSp_le hFn j)
      _ = 2 ^ 17 := by norm_num
  have hKC := le_centralizer_of_card_le hKc hHK hc.2 hQ2 hcardQ hKQ
  obtain ⟨u, hu, B, hne⟩ := Sp4Aut.exists_noncomm j hlam1
  obtain ⟨t₁, ht₁T, ht₁⟩ := hUL u hu
  have hB := spLevi_mem_perfectCore hF4 j B
  rw [← map_perfectCore_comap hα] at hB
  obtain ⟨y₁, hy₁, hy₁e⟩ := hB
  have hy₁Y : (y₁ : G) ∈ Y := by
    rw [hYdef, liftCore_eq]
    exact ⟨y₁, hy₁, rfl⟩
  have hcQ := Subgroup.commutator_mem_commutator ht₁T (Subgroup.mem_zpowers x)
  have hcomm := Subgroup.mem_centralizer_iff.mp (hKC (hYK hy₁Y)) _ hcQ
  apply hne
  have h1 : (t₁ * x₀ * t₁⁻¹ * x₀⁻¹) * y₁ = y₁ * (t₁ * x₀ * t₁⁻¹ * x₀⁻¹) := by
    apply Subtype.ext
    simpa [commutatorElement_def, hxdef] using hcomm
  have h2 := congrArg α h1
  simp only [map_mul, map_inv, ht₁, hy₁e, hx₀] at h2
  exact h2.symm

theorem step3_3_16Sp4_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) (h10 : Stmt3_3_10)
    (h14 : Stmt3_3_14_F4) (h15 : Step3_3_15RB_F4) (hJ1 : FactJ1Norm3312)
    (hGA : GriessAllModelsStatement) (hZ : FactSp4BlockZ) : Step3_3_16Sp4_F4 := by
  intro G _ _ T M L D h K _ _ hK ⟨e⟩ hb
  obtain ⟨-, F, _, _, hF, α, hαs, hαk, -⟩ := id hb
  obtain ⟨α₂, j, Kc, hα₂, hker, hmapU, hTP, hY, hinn, hO, hKc, hYK, hHK, hc⟩ :=
    sp4_config_F4 h h38 h39 h51 h10 h14 h15 hK e hF hαs hαk
  exact sp4_endgame_F4 h h14 hJ1 hGA hZ hb hF hα₂ hker hmapU j hTP hY hinn hO hKc hYK hHK hc

theorem stmt3_3_16_of_steps_F4
    (h6 : Stmt3_3_6) (h14 : Stmt3_3_14_F4) (hC32 : ASInputs.AS_C_1_32_F4) (hG2 : FactG2Cayley)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) (h10 : Stmt3_3_10)
    (h12 : Step3_3_12RB_F4) (hJ1 : FactJ1Norm3312) (hGA : GriessAllModelsStatement)
    (hZ : FactSp4BlockZ) : Stmt3_3_16_F4 :=
  stmt3_3_16_of_F4 h6 h14 hC32 hG2
    (step3_3_16SL3_of_F4 h38 h39 h51 h10 h14 (step3_3_15RB_of_F4 h6 h14 h12) hJ1)
    (step3_3_16Sp4_of_F4 h38 h39 h51 h10 h14 (step3_3_15RB_of_F4 h6 h14 h12) hJ1 hGA hZ)

end L3316

end CFSG.Quasithin.H13
