module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.ModuleIrreducible
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeDoubleCommutator
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BarMNormalizer
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairBlocks
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open Subgroup CFSG CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.Proving (barMHomSub barMHomSub_surjective ker_barMHomSub)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (mem_barM)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_zpowers_eq_bot' {X U : Subgroup G} {z : G} (hz : Odd (orderOf z))
    (hX : IsPGroup 2 ↥X) (hzX : z ∈ Subgroup.normalizer (X : Set G))
    (hXU : ⁅X, Subgroup.zpowers z⁆ ≤ U) (hU : ⁅U, Subgroup.zpowers z⁆ = ⊥) :
    ⁅X, Subgroup.zpowers z⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hX
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers z)) (Nat.card ↥X) := by
    rw [Nat.card_zpowers, hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hz)
  refine CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot X _
    (Subgroup.zpowers_le.mpr hzX) hcop (le_bot_iff.mp ?_)
  calc ⁅⁅X, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ ≤ ⁅U, Subgroup.zpowers z⁆ :=
        Subgroup.commutator_mono hXU le_rfl
    _ = ⊥ := hU

omit [Finite G] in
theorem commutator_facts {L V : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hV : CFSG.Open.IsElemAbelian 2 V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hVL : V ≤ Subgroup.normalizer (L : Set G)) :
    ⁅V, L⁆ ≤ V ∧ L ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) ∧
      (∀ a ∈ ⁅V, L⁆, ∀ b ∈ ⁅V, L⁆, a * b = b * a) ∧ (∀ a ∈ ⁅V, L⁆, a ^ 2 = 1) ∧
      ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆ := by
  have hWV : ⁅V, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have h1 : l * v⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv)
    have : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
    rw [this]; exact V.mul_mem hv h1
  exact ⟨hWV, le_normalizer_commutator' hLV Subgroup.le_normalizer,
    fun a ha b hb => elemAbelian_comm' hV a (hWV ha) b (hWV hb),
    fun a ha => hV.2 a (hWV ha), commutator_commutator_eq_of_perfect' hperf hLV hVL⟩

theorem center_barM_eq_bot {M L V : Subgroup G} (hLs : IsTwoPrimeComponent M L)
    (hidx : (Subgroup.center ↥(barM M L)).index = 2520)
    (hodd : Odd (Nat.card (Subgroup.center ↥(barM M L))))
    (hV : CFSG.Open.IsElemAbelian 2 V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hVL : V ≤ Subgroup.normalizer (L : Set G)) (h16 : Nat.card ↥⁅V, L⁆ = 2 ^ 4)
    (hchar : CharTwo M) (hQV : ⁅pCoreOf 2 M, L⁆ ≤ V) :
    Subgroup.center ↥(barM M L) = ⊥ := by
  classical
  have hLM : L ≤ M := hLs.le
  set Q : Subgroup G := pCoreOf 2 M with hQ
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hQ2 : IsPGroup 2 Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
  obtain ⟨hWV, hWL, hWc, hW2, hWW⟩ := commutator_facts hLs.perfect hV hLV hVL
  set W : Subgroup G := ⁅V, L⁆ with hWdef
  have hWne : W ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥W = 1 := by rw [h]; exact Subgroup.card_bot
    rw [h16] at h1
    norm_num at h1
  have hW16 : Nat.card ↥W = 16 := h16
  have hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLs.perfect
  have hq := hLs.component.2.2
  set ψ := barMHomSub hLM with hψ
  have hψs : Function.Surjective ψ := barMHomSub_surjective hLM
  set ρ := conjActHom L W hWL with hρ
  set Z := Subgroup.center ↥(barM M L) with hZ
  have hzK : ∀ z ∈ Z, z ∈ ρ.ker.map ψ := by
    intro z hz
    have hKn : (ρ.ker.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψs
    rcases CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.normal_le_center_or_eq_top hq.1
      hq.2 (ρ.ker.map ψ) hKn with hc | htop
    · have h1 : (ρ.ker.map ψ).index ∣ 20160 := by
        have e1 : (ρ.ker.map ψ).index = ((ρ.ker.map ψ).comap ψ).index :=
          (Subgroup.index_comap_of_surjective _ hψs).symm
        have e2 : ((ρ.ker.map ψ).comap ψ).index ∣ ρ.ker.index :=
          Subgroup.index_dvd_of_le (Subgroup.le_comap_map ψ ρ.ker)
        have e3 : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
        have e4 : Nat.card ρ.range ∣ Nat.card (MulAut ↥W) := Subgroup.card_subgroup_dvd_card _
        have e5 : Nat.card (MulAut ↥W) = 20160 :=
          card_mulAut_sixteen (fun a b => Subtype.ext (hWc a a.2 b b.2))
            (fun a => Subtype.ext (hW2 a a.2)) hW16
        rw [e1]
        exact e2.trans (e3 ▸ e5 ▸ e4)
      have h2 := Subgroup.relIndex_mul_index hc
      rw [hidx] at h2
      have h3 : (ρ.ker.map ψ).relIndex Z ∣ 8 := by
        have : (ρ.ker.map ψ).relIndex Z * 2520 ∣ 8 * 2520 := by
          rw [h2]; norm_num; exact h1
        exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
      have h4 : (ρ.ker.map ψ).relIndex Z ∣ Nat.card Z := by
        have := Subgroup.index_dvd_card ((ρ.ker.map ψ).subgroupOf Z)
        exact this
      have h5 : Odd ((ρ.ker.map ψ).relIndex Z) := hodd.of_dvd_nat h4
      have h6 : Nat.Coprime ((ρ.ker.map ψ).relIndex Z) 8 := by
        have : Nat.Coprime ((ρ.ker.map ψ).relIndex Z) 2 := Nat.coprime_two_right.mpr h5
        exact Nat.Coprime.pow_right 3 this
      have h7 : (ρ.ker.map ψ).relIndex Z = 1 := Nat.Coprime.eq_one_of_dvd h6 h3
      exact (Subgroup.relIndex_eq_one.mp h7) hz
    · exfalso
      have h1 : ρ = 1 := eq_one_of_map_ker_eq_top hperfL ψ (isPGroup_ker_barMHomSub hLM) ρ htop
      apply hWne
      rw [← hWW]
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro w hw l hl
      have := congrArg (fun f => ((f ⟨w, hw⟩ : ↥W) : G)) (congrArg (fun f => f ⟨l, hl⟩) h1)
      simp only [MonoidHom.one_apply] at this
      have e : (l : G) * w * (l : G)⁻¹ = w := by
        rw [coe_conjActHom] at this ; exact this
      rw [Subgroup.mem_bot, commutatorElement_def]
      rw [show w * l * w⁻¹ * l⁻¹ = w * (l * w⁻¹ * l⁻¹) by group]
      have e' : l * w⁻¹ * l⁻¹ = w⁻¹ := by
        have := congrArg (fun x => x⁻¹) e
        simpa [mul_assoc] using this
      rw [e']; simp
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.1 (hzK z hz)
  have hρk : ρ k = 1 := hk
  have hzord : Odd (orderOf z) := by
    have h1 : orderOf (⟨z, hz⟩ : Subgroup.center ↥(barM M L)) ∣
        Nat.card (Subgroup.center ↥(barM M L)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hodd.of_dvd_nat h1
  obtain ⟨a, b, hb, hordk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  set k' : ↥L := k ^ 2 ^ a with hk'
  have hordk' : orderOf k' = b := by
    rw [hk', orderOf_pow_of_dvd (by positivity) (hordk ▸ dvd_mul_right _ _), hordk,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hρk' : ρ k' = 1 := by rw [hk', map_pow, hρk, one_pow]
  have hψk' : ψ k' = z ^ 2 ^ a := by rw [hk', map_pow, hkz]
  have hkQ : (k' : G) ∈ Q := by
    set y : G := (k' : G) with hy
    have hyL : y ∈ L := k'.2
    have hyM : y ∈ M := hLM hyL
    have hyord : Odd (orderOf y) := by
      rw [hy, Subgroup.orderOf_coe, hordk']; exact hb
    have hyC : y ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 : ρ k' ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [hρk']; rfl
      have h2 := congrArg Subtype.val h1
      rw [coe_conjActHom] at h2
      have h3 : y * w * y⁻¹ = w := h2
      calc w * y = (y * w * y⁻¹) * y := by rw [h3]
        _ = y * w := by group
    set R : Subgroup G := Subgroup.zpowers y with hR
    have hRL : R ≤ L := Subgroup.zpowers_le.mpr hyL
    have hRW : ⁅V, R⁆ ≤ W := Subgroup.commutator_mono le_rfl hRL
    have hWR : ⁅W, R⁆ = ⊥ := by
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      exact Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hyC)
    have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
    have hVR : ⁅V, R⁆ = ⊥ := commutator_zpowers_eq_bot' hyord hV2 (hLV hyL) hRW hWR
    have hQR : ⁅Q, R⁆ ≤ V := (Subgroup.commutator_mono le_rfl hRL).trans hQV
    have hQR0 : ⁅Q, R⁆ = ⊥ := commutator_zpowers_eq_bot' hyord hQ2 (hMQ hyM) hQR hVR
    have hyCQ : y ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQR0 hq
      exact (Subgroup.mem_centralizer_iff.mp this y (Subgroup.mem_zpowers y)).symm
    exact hchar ⟨hyM, hyCQ⟩
  have hz2 : z ^ 2 ^ a = 1 := by
    rw [← hψk']
    have : k' ∈ ψ.ker := by
      rw [hψ, ker_barMHomSub hLM]
      exact hkQ
    exact this
  have hdvd : orderOf z ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hz2
  have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hzord)) hdvd
  rw [orderOf_eq_one_iff.mp h1]
  exact Subgroup.one_mem _

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
