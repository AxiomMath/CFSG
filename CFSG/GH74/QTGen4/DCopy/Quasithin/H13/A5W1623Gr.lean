module

public import CFSG.Quasithin.H13.A5W1623Gr
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1623End
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1623Hb

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem lambda2_of_extSq_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {K : Subgroup G} (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (hLvK : S.Lv ≤ K) (hKW : K ≤ Subgroup.normalizer (S.WK K : Set G))
    [IsMulCommutative ↥(S.WK K)] (hV2 : ∀ v : ↥(S.WK K), v ^ 2 = 1)
    {α : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2)} (hαs : Function.Surjective α)
    (hαC : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G))
    (hmapU : ((S.Tv ⊓ K).subgroupOf K).map α = unitriangular 4 (ZMod 2))
    (hgr : ∃ t ∈ S.Tv, ∃ u ∈ unitriangular 4 (ZMod 2), ∀ (l : ↥K) (h : t * l * t⁻¹ ∈ K),
      α ⟨t * l * t⁻¹, h⟩ = graphAut 4 (u * α l * u⁻¹))
    {u : ↥(S.WK K)} (hu : u ∈ commV (S.plus K))
    (hfix : ∀ k : ↥K,
      ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) u = u ↔
        (k : G) ∈ Subgroup.centralizer ({S.z} : Set G))
    {π : ↥(StatedSL 4 (ZMod 2)) →* ↥(S.plus K)}
    (hπ : (FFModel.extSq (ZMod 2) 4).RealizesVia (S.plus K) (commV (S.plus K))
      (fixV (S.plus K) ⊓ commV (S.plus K)) π) :
    ((K ⊓ Subgroup.centralizer ({S.z} : Set G)).subgroupOf K).map α =
        flagStabilizer 4 (ZMod 2) {2} ∧
      ∀ B : Subgroup G, B ≤ pCoreOf 2 (K ⊓ Subgroup.centralizer ({S.z} : Set G)) →
        ¬ B ≤ Subgroup.centralizer (S.WK K : Set G) →
        (B ⊓ Subgroup.centralizer (S.WK K : Set G)).relIndex B <
          (S.WK K ⊓ Subgroup.centralizer (B : Set G)).relIndex (S.WK K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := S.WK K with hWdef
  set φ' : ↥K →* MulAut ↥W := (autOn K W).subtype.comp (InternalSec.autOnHom hKW) with hφ'
  obtain ⟨D⟩ := FLc.vmodelExtSq hπ (fun g hg z hz => hz.1 g hg)
  have hρi : Function.Injective (FLc.rhoOf π) :=
    rhoOf_injective_of (FFC.injective_of_faithful_sec (FFC.extSq_faithful (by norm_num)) hπ)
  set ρ := FLc.rhoOf π with hρ
  obtain ⟨g, u', hu', hcase⟩ := exists_conj_form hKW hαs hαC (FLc.rhoOf_mem π)
    (FLc.rhoOf_surj hπ.1) hρi
  have hvf := S.conj_unitriangular_fix hKW hfix hmapU hu' hcase
  set Hz := ((K ⊓ Subgroup.centralizer ({S.z} : Set G)).subgroupOf K).map α with hHz
  have hUH := S.unitriangular_le_map_centralizer_z hmapU

  have hr13 := S.reflection_mem_of_model hKW hαs hfix hmapU hu' hcase (I := {1, 3})
    (by
      intro i hi
      rcases hi with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl)
    (fun i hi hiI => D.fix_reflection_conj hV2 (by norm_num) FLc.fix_extSq4 g hu hvf hi (by
      rcases hiI with rfl | rfl <;> norm_num))
  have hQ : flagStabilizer 4 (ZMod 2) {2} ≤ Hz := by
    refine FLc.QI_le_of_reflections hUH fun i hi hi2 => hr13 i hi ?_
    have h1 := hi.1
    have h2 := hi.2
    have : i = 1 ∨ i = 3 := by omega
    rcases this with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hr2 := S.reflection_two_not_mem_F4 h1222 h517 hT hLvK hαC hmapU hgr
  have hHz2 : Hz ≤ flagStabilizer 4 (ZMod 2) {2} := by
    refine (FLc.eq_QI_cuts hUH).trans_le ((FLc.QI_le_QI_iff fun j hj => ?_).mpr fun j hj => ?_)
    · rw [Set.mem_singleton_iff.mp hj]
      exact ⟨by norm_num, by norm_num⟩
    · rw [Set.mem_singleton_iff.mp hj]
      exact ⟨by norm_num, by norm_num, hr2⟩
  have hEq : Hz = flagStabilizer 4 (ZMod 2) {2} := le_antisymm hHz2 hQ
  refine ⟨hEq, fun B hB hBW => ?_⟩
  have hO := CFSG.LieType.BorelTits.pCoreOf_le 2 (K ⊓ Subgroup.centralizer ({S.z} : Set G))
  have hBK : B ≤ K := hB.trans (hO.trans inf_le_left)
  have hBN : B ≤ Subgroup.normalizer (W : Set G) := hBK.trans hKW

  have hαB : ∀ b : ↥K, (b : G) ∈ B → α b ∈ Ln2P.flagRadical 4 (ZMod 2) 2 := by
    intro b hb
    apply Ln2P.pCoreOf_le_flagRadical
    set P' := ((pCoreOf 2 (K ⊓ Subgroup.centralizer ({S.z} : Set G))).subgroupOf K).map α
      with hP'
    have hP'Q : P' ≤ flagStabilizer 4 (ZMod 2) {2} := by
      rw [← hEq]
      exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr (hO hx)
    have hP'2 : IsPGroup 2 ↥P' := by
      refine IsPGroup.map ?_ α
      exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).of_equiv
        (Subgroup.subgroupOfEquivOfLe (hO.trans inf_le_left)).symm
    have hP'n : flagStabilizer 4 (ZMod 2) {2} ≤
        Subgroup.normalizer (P' : Set (SpecialLinearGroup (Fin 4) (ZMod 2))) := by
      rw [← hEq]
      rintro _ ⟨c, hc, rfl⟩
      apply L3316.mem_normalizer_of_map_le
      rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      refine ⟨c * m * c⁻¹, ?_, by simp [map_mul, map_inv]⟩
      have hm' : ((m : ↥K) : G) ∈ pCoreOf 2 (K ⊓ Subgroup.centralizer ({S.z} : Set G)) := hm
      have hc' : (c : G) ∈ K ⊓ Subgroup.centralizer ({S.z} : Set G) := hc
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hc') (m : G)).mp hm'
      show ((c * m * c⁻¹ : ↥K) : G) ∈ pCoreOf 2 (K ⊓ Subgroup.centralizer ({S.z} : Set G))
      simpa using h1
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hP'Q hP'n hP'2
      ⟨b, Subgroup.mem_subgroupOf.mpr (hB hb), rfl⟩

  set AB := (B.subgroupOf K).map φ' with hABdef
  have hAB : AB = autOn B W := map_autOnHom_eq_autOn hKW hBK
  set A : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    AB.comap (ρ.comp (MulAut.conj g).toMonoidHom) with hAdef
  have hrad := fun (b : ↥K) (hb : b ∈ B.subgroupOf K) =>
    S.exists_conj_radical hKW hu' hcase b (hαB b (Subgroup.mem_subgroupOf.mp hb))
  have hAR : A ≤ Ln2P.flagRadical 4 (ZMod 2) 2 := by
    intro y hy
    obtain ⟨b, hb, hbe⟩ := hy
    obtain ⟨y', hy'R, hy'⟩ := hrad b hb
    have h1 : g * y' * g⁻¹ = g * y * g⁻¹ := hρi (hy'.trans hbe)
    have h2 : y' = y := by
      have := congrArg (fun x => g⁻¹ * x * g) h1
      simpa [mul_assoc] using this
    rw [← h2]
    exact hy'R
  have hAmap : A.map ρ = AB.map (MulAut.conj (ρ g)⁻¹).toMonoidHom := by
    ext a
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨ρ (g * y * g⁻¹), hy, ?_⟩
      show (ρ g)⁻¹ * ρ (g * y * g⁻¹) * ((ρ g)⁻¹)⁻¹ = ρ y
      rw [map_mul, map_mul, map_inv, inv_inv]
      group
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨y', -, hy'⟩ := hrad b hb
      refine ⟨y', ?_, ?_⟩
      · show ρ (g * y' * g⁻¹) ∈ AB
        rw [hy']
        exact ⟨b, hb, rfl⟩
      · show ρ y' = (ρ g)⁻¹ * φ' b * ((ρ g)⁻¹)⁻¹
        have e1 : φ' b = ρ (g * y' * g⁻¹) := hy'.symm
        rw [e1, map_mul, map_mul, map_inv, inv_inv]
        group

  have hA : A ≠ ⊥ := by
    intro hbot
    apply hBW
    intro b hb
    obtain ⟨y', -, hy'⟩ := hrad ⟨b, hBK hb⟩ (Subgroup.mem_subgroupOf.mpr hb)
    have hyA : y' ∈ A := by
      show ρ (g * y' * g⁻¹) ∈ AB
      rw [hy']
      exact ⟨⟨b, hBK hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hyA
    rw [hyA, mul_one, mul_inv_cancel, map_one] at hy'
    have h1 : InternalSec.autOnHom hKW ⟨b, hBK hb⟩ = 1 := Subtype.ext hy'.symm
    exact (InternalSec.mem_ker_autOnHom hKW _).mp (MonoidHom.mem_ker.mpr h1)

  have hmain := FLc.not_ff_ext4 hρi D A
    (fun y hy => (Ln2P.mem_unitriangular_of_mem_flagRadical (hAR hy)).1)
    (fun y hy i j hij hd => by
      obtain ⟨-, h01, h23⟩ := Ln2P.mem_unitriangular_of_mem_flagRadical (hAR hy)
      have hd2 := hd 2 rfl
      fin_cases i <;> fin_cases j <;>
        first
          | exact absurd hij (by decide)
          | exact h01
          | exact h23
          | exact absurd (hd2 (by decide)) (by decide))
    hA
  rw [hAmap, Subgroup.card_map_of_injective (MulAut.conj (ρ g)⁻¹).injective,
    card_fixV_map_conj, hAB, card_autOn_eq_relIndex hBN, card_fixV_autOn hBN] at hmain
  have h1 := Subgroup.relIndex_mul_card (W ⊓ Subgroup.centralizer (B : Set G)) W
  rw [show W ⊓ Subgroup.centralizer (B : Set G) ⊓ W = W ⊓ Subgroup.centralizer (B : Set G) from
    inf_eq_left.mpr inf_le_left] at h1
  rw [← h1] at hmain
  exact Nat.lt_of_mul_lt_mul_right hmain

theorem graph_lambda2_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (h51 : AsB51) (hH : S.Hyp1367) {K : Subgroup G} (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) (hLvK : S.Lv ≤ K)
    (hker : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (S.WK K : Set G)))
    {α : ↥K →* SpecialLinearGroup (Fin 4) (ZMod 2)} (hαs : Function.Surjective α)
    (hαC : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G))
    (hmapU : ((S.Tv ⊓ K).subgroupOf K).map α = unitriangular 4 (ZMod 2))
    (hgr : ∃ t ∈ S.Tv, ∃ u ∈ unitriangular 4 (ZMod 2), ∀ (l : ↥K) (h : t * l * t⁻¹ ∈ K),
      α ⟨t * l * t⁻¹, h⟩ = graphAut 4 (u * α l * u⁻¹)) :
    ((K ⊓ Subgroup.centralizer ({S.z} : Set G)).subgroupOf K).map α =
        flagStabilizer 4 (ZMod 2) {2} ∧
      ∀ B : Subgroup G, B ≤ pCoreOf 2 (K ⊓ Subgroup.centralizer ({S.z} : Set G)) →
        ¬ B ≤ Subgroup.centralizer (S.WK K : Set G) →
        (B ⊓ Subgroup.centralizer (S.WK K : Set G)).relIndex B <
          (S.WK K ⊓ Subgroup.centralizer (B : Set G)).relIndex (S.WK K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hH.hF
  have hKG := hYz.1
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hKG hT
  have : IsMulCommutative ↥(S.WK K) := hR.2.2.1.1
  have hV2 : ∀ v : ↥(S.WK K), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hR.2.2.1.2 v v.2)
  have hKH : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKW : K ≤ Subgroup.normalizer (S.WK K : Set G) := hKH.trans hR.2.1
  set φ' : ↥K →* MulAut ↥(S.WK K) :=
    (autOn K (S.WK K)).subtype.comp (InternalSec.autOnHom hKW) with hφ'

  obtain ⟨e, -⟩ := exists_mulEquiv_autOn hKW hαs hαC
  have hcardN : Nat.card ↥(S.plus K) = 20160 := by
    calc Nat.card ↥(S.plus K) = Nat.card (SpecialLinearGroup (Fin 4) (ZMod 2)) :=
          Nat.card_congr e.toEquiv
      _ = Nat.card ↥(StatedSL 4 (ZMod 2)) :=
          Nat.card_congr (specialLinearGroupEquivStatedSL 4 (ZMod 2)).toEquiv
      _ = 20160 := card_statedSL_four_zmod1527d
  have hN : Nat.card ↥(S.plus K) = 20160 ∨ Nat.card ↥(S.plus K) = 9999360 := Or.inl hcardN

  have hzW : S.z ∈ S.WK K := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  have hsylH : IsSylowTwoOf S.Tv (K ⊔ S.Tv) :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right
      (sup_le hKG S.Tv_le_Gv)
  have hSK : IsSylowTwoOf (S.Tv ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hsylH le_sup_left (sup_le Subgroup.le_normalizer hT)
  have hSN := Setup.Wreath.isSylowTwoOf_map_hom hSK φ'
  have hrange : φ'.range = autOn K (S.WK K) := by
    rw [hφ', MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      (InternalSec.autOnHom_surjective hKW), ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hrange] at hSN
  have hSz : ∀ s ∈ ((S.Tv ⊓ K).subgroupOf K).map φ', s ⟨S.z, hzW⟩ = ⟨S.z, hzW⟩ := by
    rintro _ ⟨t, ht, rfl⟩
    apply Subtype.ext
    show ((((InternalSec.autOnHom hKW t : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K))
      ⟨S.z, hzW⟩ : ↥(S.WK K)) : G) = S.z
    rw [coe_autOnHom_apply]
    exact S.conj_z_of_mem_T
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ht)).1).1
  have hNn : ∀ x ∈ autOn K (S.WK K), ∀ l ∈ autOn K (S.WK K), x * l * x⁻¹ ∈ autOn K (S.WK K) :=
    fun x hx l hl => Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hl) (Subgroup.inv_mem _ hx)
  obtain ⟨u, w, hzuw, hu, hw, -⟩ :=
    S153L.exists_split_of_fixed hV2 le_rfl hNn hSN le_sup_left hSz
  replace hu : u ∈ commV (S.plus K) := hu
  have hzuw' : S.z = (u : G) * w := congrArg Subtype.val hzuw
  have hw' : ∀ k : ↥K,
      ((InternalSec.autOnHom hKW k : ↥(autOn K (S.WK K))) : MulAut ↥(S.WK K)) w = w :=
    fun k => hw _ (InternalSec.autOnHom hKW k).2
  have hfix := S.fix_iff_centralizer_z hKW hzuw' hw'

  have hr2 := S.reflection_two_not_mem_F4 h1222 h517 hT hLvK hαC hmapU hgr
  have hnat : ∀ {ρ : SpecialLinearGroup (Fin 4) (ZMod 2) →* MulAut ↥(S.WK K)},
      (∀ x, ρ x ∈ S.plus K) → (∀ n ∈ S.plus K, ∃ x, ρ x = n) → Function.Injective ρ →
      (∀ g : SpecialLinearGroup (Fin 4) (ZMod 2),
        (∀ s ∈ unitriangular 4 (ZMod 2), ρ (g * s * g⁻¹) u = u) →
        ρ (g * reflection 4 (ZMod 2) 2 (by norm_num) (by norm_num) * g⁻¹) u = u) → False := by
    intro ρ hρN hρs hρi hmodel
    obtain ⟨g, u', hu', hcase⟩ := exists_conj_form hKW hαs hαC hρN hρs hρi
    have hvf := S.conj_unitriangular_fix hKW hfix hmapU hu' hcase
    apply hr2
    refine S.reflection_mem_of_model hKW hαs hfix hmapU hu' hcase (I := {2})
      (fun i hi => by rw [Set.mem_singleton_iff.mp hi]; rfl)
      (fun i hi hiI => ?_) 2 ⟨by norm_num, by norm_num⟩ rfl
    obtain rfl : i = 2 := hiI
    exact hmodel g hvf
  have hbot : ∀ g ∈ S.plus K, ∀ z ∈ (⊥ : Subgroup ↥(S.WK K)), g z = z := fun g _ z hz => by
    rw [Subgroup.mem_bot.mp hz, map_one]

  have hB51 := S.b51Hyp_plus_F4 h1222 h517 hH hYz hT hLvK hker
  obtain ⟨hp1, -⟩ := h51 ↥(S.WK K) hV2 _ _ hB51
  rcases hp1.2 with hi | hii | ⟨n, hiii⟩ | hiv
  ·
    obtain ⟨-, hpair, -⟩ := hi
    rcases hpair with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
    · exact (not_binaryNaturalSL_two1527d hN h).elim
    · exact (not_binaryNaturalSL_three1527d hN h).elim
    · exact (not_binaryNaturalSp4_1527d hN h).elim
    · exact (not_g2Natural1527d hN h).elim
    · exact (not_g2NaturalDerived_one1527d hN h).elim
    · refine (not_alternatingNatural1527d (n := 5) (by norm_num) ?_ h).elim
      rw [hcardN]
      norm_num [Nat.factorial]
    · refine (not_alternatingNatural1527d (n := 6) (by norm_num) ?_ h).elim
      rw [hcardN]
      norm_num [Nat.factorial]
    · refine (not_alternatingNatural1527d (n := 7) (by norm_num) ?_ h).elim
      rw [hcardN]
      norm_num [Nat.factorial]
    · exact (not_a7Four1527d hN h).elim
    · exact (not_tripleA6Six1527d hN h).elim
    ·
      exfalso
      obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
      obtain ⟨D⟩ := FLc.vmodelNat hπ (fun g hg z hz => hz.1 g hg)
      have hπi := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
      refine hnat (FLc.rhoOf_mem π) (FLc.rhoOf_surj hπ.1) (rhoOf_injective_of hπi)
        fun g hvf => ?_
      exact D.fix_reflection_conj hV2 (by norm_num) FLc.fix_nat g hu hvf
        ⟨by norm_num, by norm_num⟩ (by norm_num)
    ·
      exfalso
      obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
      have := card_eq_of_nat_realizes1527d hπ
      rw [hcardN, card_statedSL_five_zmod1527d] at this
      omega
    ·
      obtain ⟨π, hπ⟩ := h
      exact S.lambda2_of_extSq_F4 h1222 h517 hT hLvK hKW hV2 hαs hαC hmapU hgr hu hfix hπ
    ·
      exfalso
      obtain ⟨π, hπ⟩ := h
      have hπi := FFC.injective_of_faithful_sec (FFC.extSq_faithful (by norm_num)) hπ
      have : Nat.card ↥(StatedSL 5 (ZMod 2)) = Nat.card ↥(S.plus K) :=
        Nat.card_congr (Equiv.ofBijective π ⟨hπi, hπ.1⟩)
      rw [card_statedSL_five_zmod1527d, hcardN] at this
      omega
  ·
    exfalso
    obtain ⟨-, n, F, _, _, hF, I, π, -, -, hreal, -⟩ := hii
    exact ne_card_sl3_1527d hF (N := Nat.card ↥(S.plus K)) hN
      (card_eq_of_nat_realizes1527d (hreal 0)).symm
  ·
    exfalso
    obtain ⟨-, hn45, π, U₁, U₂, ⟨hsup, hinf⟩, h₁, h₂⟩ := hiii
    rcases hn45 with rfl | rfl
    · obtain ⟨D₁⟩ := FLc.vmodelNat h₁ hbot
      obtain ⟨D₂⟩ := FLc.vmodelDual h₂ hbot
      have hπi := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) h₁
      refine hnat (FLc.rhoOf_mem π) (FLc.rhoOf_surj h₁.1) (rhoOf_injective_of hπi)
        fun g hvf => ?_
      rw [← hsup] at hu
      obtain ⟨u₁, hu₁, u₂, hu₂, hu12⟩ := Subgroup.mem_sup.mp hu
      rw [← hu12] at hvf ⊢
      have hcomp : ∀ s ∈ unitriangular 4 (ZMod 2),
          FLc.rhoOf π (g * s * g⁻¹) u₁ = u₁ ∧ FLc.rhoOf π (g * s * g⁻¹) u₂ = u₂ := by
        intro s hs
        have h := hvf s hs
        rw [map_mul (FLc.rhoOf π (g * s * g⁻¹)) u₁ u₂] at h
        have h1 := D₁.inv (g * s * g⁻¹) u₁ hu₁
        have h2 := D₂.inv (g * s * g⁻¹) u₂ hu₂
        have e : FLc.rhoOf π (g * s * g⁻¹) u₁ * u₁⁻¹ =
            u₂ * (FLc.rhoOf π (g * s * g⁻¹) u₂)⁻¹ := by
          rw [eq_mul_inv_of_mul_eq h, mul_right_comm (u₁ * u₂), mul_right_comm u₁ u₂ u₁⁻¹,
            mul_inv_cancel, one_mul]
        have hx : FLc.rhoOf π (g * s * g⁻¹) u₁ * u₁⁻¹ ∈ U₁ ⊓ U₂ :=
          ⟨U₁.mul_mem h1 (U₁.inv_mem hu₁), e ▸ U₂.mul_mem hu₂ (U₂.inv_mem h2)⟩
        rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at hx
        refine ⟨hx, ?_⟩
        rw [hx] at h
        exact mul_left_cancel h
      have hf₁ := D₁.fix_reflection_conj hV2 (by norm_num) FLc.fix_nat g hu₁
        (fun s hs => (hcomp s hs).1) (i := 2) ⟨by norm_num, by norm_num⟩ (by norm_num)
      have hf₂ := D₂.fix_reflection_conj hV2 (by norm_num) (FLc.fix_dual (by norm_num)) g hu₂
        (fun s hs => (hcomp s hs).2) (i := 2) ⟨by norm_num, by norm_num⟩ (by norm_num)
      rw [map_mul (FLc.rhoOf π (g * reflection 4 (ZMod 2) 2 (by norm_num) (by norm_num) * g⁻¹))
        u₁ u₂, hf₁, hf₂]
    · have := card_eq_of_nat_realizes1527d h₁
      rw [hcardN, card_statedSL_five_zmod1527d] at this
      omega
  ·
    exfalso
    obtain ⟨-, n, hn45, k, hk1, -, hdir⟩ := hiv
    obtain ⟨I, π, -, hind, hsup, hreal⟩ := hdir
    rcases hn45 with rfl | rfl
    · have D : ∀ j, FLc.VModel 4 (FLc.rhoOf π) (I j) ⊥ (Multiplicative (FLc.Vt 4))
          (fun g a => FLc.actM g a) := fun j => Classical.choice (FLc.vmodelNat (hreal j) hbot)
      have hindep : iSupIndep I := by
        intro i
        have := hind i
        rw [bot_sup_eq] at this
        exact disjoint_iff.2 this
      have hsup' : commV (S.plus K) = ⨆ j, I j := by rw [← hsup, bot_sup_eq]
      have hπi := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) (hreal ⟨0, hk1⟩)
      refine hnat (FLc.rhoOf_mem π) (FLc.rhoOf_surj (hreal ⟨0, hk1⟩).1)
        (rhoOf_injective_of hπi) fun g hvf => ?_
      rw [hsup'] at hu
      exact FLc.fix_reflection_sum hindep D hV2 (by norm_num)
        (fun a ha i hi hic => FLc.fix_nat a ha i hi hic) g hu hvf ⟨by norm_num, by norm_num⟩
        (by norm_num)
    · have := card_eq_of_nat_realizes1527d (hreal ⟨0, hk1⟩)
      rw [hcardN, card_statedSL_five_zmod1527d] at this
      omega

end Setting

theorem graph1367Lambda2_of_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hGA : GriessAllModelsStatement) (h51 : AsB51) :
    Graph1367Lambda2_F4 := by
  intro G _ _ T L V S hH K hK hYz hT hLvK α hαs hαC hmapU hgr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hH.hF hYz.1 hT
  have hKW : K ≤ Subgroup.normalizer (S.WK K : Set G) :=
    (le_sup_left.trans le_sup_left).trans hR.2.1
  obtain ⟨e, -⟩ := exists_mulEquiv_autOn hKW hαs hαC
  have hq := S.kbar_isQuasisimple_of_sl_F4 h1222 h517 hH.hF h36 h37 h38 hK hYz hT (Or.inl rfl) e
  obtain ⟨α', -, hα'k, hα'C⟩ := S.exists_slHom_plus_F4 h1222 h517 hGA hH.hF hYz.1 hT
    (fun x hx => Subgroup.le_normalizer (hLvK hx)) hq (by norm_num) (by norm_num) e
  have hker : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (S.WK K : Set G)) := by
    rintro ⟨x, hxK, hxC⟩
    have h1 : (⟨x, hxK⟩ : ↥K) ∈ α'.ker := MonoidHom.mem_ker.mpr ((hα'C _).mpr hxC)
    rw [hα'k] at h1
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, h1⟩
    refine ⟨m, Subtype.ext ?_⟩
    have := congrArg Subtype.val (congrArg Subtype.val hm)
    simpa using this
  exact S.graph_lambda2_F4 h1222 h517 h51 hH hYz hT hLvK hker hαs hαC hmapU hgr

theorem lemma13623C_of_b51_F4
    (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h132 : ASInputs.AS_C_1_32_F4) (h134 : C134L32Corr_F4)
    (hres : Lem13622Case4Z0_F4) (hGA : GriessAllModelsStatement) (h620 : Lemma13620L45_F4)
    (hO3 : O3Prime1367_F4) (h51 : AsB51) : Lemma13623C_F4 :=
  lemma13623C_of_lambda2_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h36 h37 h38 h39 h132 h134
    hres hGA h620 hO3 (graph1367Lambda2_of_F4 h1222 h517 h36 h37 h38 hGA h51)

end CFSG.Quasithin.H13.A5
