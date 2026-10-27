module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig
public import CFSG.Quasithin.Vol2.KGFactC31Hex
public import CFSG.Quasithin.AppendixH.H14.H141Octad
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Main
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Perf

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open
open CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

private theorem seven_dvd_card_alt_eight : 7 ∣ Nat.card (alternatingGroup (Fin 8)) := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem seven_dvd_card_alt_seven : 7 ∣ Nat.card (alternatingGroup (Fin 7)) := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem seven_dvd_card_GL_three :
    7 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
  have h : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_three, ZMod.card]
    norm_num
  rw [h]
  norm_num

private theorem not_isPerfect_z3_mul_alt_five :
    ¬ Group.IsPerfect (Multiplicative (ZMod 3) × alternatingGroup (Fin 5)) := by
  intro hp
  haveI := hp
  have h1 : Group.IsPerfect (Multiplicative (ZMod 3)) :=
    Group.IsPerfect.ofSurjective
      (f := MonoidHom.fst (Multiplicative (ZMod 3)) (alternatingGroup (Fin 5)))
      (fun x => ⟨(x, 1), rfl⟩)
  haveI := h1
  haveI : IsMulCommutative (Multiplicative (ZMod 3)) := ⟨⟨fun a b => mul_comm a b⟩⟩
  have : Subsingleton (Multiplicative (ZMod 3)) :=
    Group.IsPerfect.subsingleton_of_isMulCommutative
  have h2 : (Multiplicative.ofAdd (1 : ZMod 3) : Multiplicative (ZMod 3)) ≠ 1 := by decide
  exact h2 (Subsingleton.elim _ _)

theorem KConfig.sixteen_list
    {G : Type} [Group G] [Finite G] {L V MK : Subgroup G}
    (h : KConfig G L V MK) (hV : Nat.card V = 16) (hC : Subgroup.centralizer (V : Set G) ≤ V)
    (h7 : ∀ n ∈ Subgroup.normalizer (V : Set G),
      (∀ v ∈ V, n ^ 7 * v * (n ^ 7)⁻¹ = v) → ∀ v ∈ V, n * v * n⁻¹ = v) :
    CFSG.Open.pCoreOf 2 L = V ∧
      (Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 6)) ∨
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 5))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pCoreOf 2 L = V := le_antisymm (h.pCoreOf_le.trans hC) h.le_pCoreOf
  have hpck : CFSG.pCore 2 ↥L = V.subgroupOf L := by
    rw [← CFSG.Quasithin.KGC31.Hex.pCoreOf_subgroupOf' L, hO]
  have hLnotV : ¬ L ≤ V := by
    intro hLV
    have hmono : ⁅V, L⁆ ≤ ⁅V, V⁆ := Subgroup.commutator_mono le_rfl hLV
    have hVV : ⁅V, V⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.le_centralizer_iff_isMulCommutative.mpr h.elemAbelian.1
    rw [hVV, le_bot_iff] at hmono
    exact h.ne_bot (by rw [h.eq_commutator, hmono])
  letI : IsMulCommutative ↥V := h.elemAbelian.1
  obtain ⟨e⟩ := CFSG.Quasithin.AppendixH.H14.exists_mulEquiv_elemAbelian_two (G := G) V
    h.elemAbelian 4 (by rw [hV]; norm_num)
  let φ : ↥L →* MulAut ↥V := (CFSG.Quasithin.conjAct V).comp (Subgroup.inclusion h.le_normalizer)
  let ψ : ↥L →* MulAut (E2 4) := (MulAut.congr e).toMonoidHom.comp φ
  have hφker : φ.ker = V.subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
      CFSG.Quasithin.AutOn.conjAct_eq_one_iff]
    exact ⟨fun hl => hC hl,
      fun hl => Subgroup.le_centralizer_iff_isMulCommutative.mpr h.elemAbelian.1 hl⟩
  have hψker : ψ.ker = φ.ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact MulEquiv.map_eq_one_iff (MulAut.congr e)
  have hle : CFSG.pCore 2 ↥L ≤ ψ.ker := by rw [hpck, hψker, hφker]
  let ι : (↥L ⧸ CFSG.pCore 2 ↥L) →* MulAut (E2 4) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) ψ hle
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) q
    change ψ l = 1 at hq
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hl : l ∈ ψ.ker := MonoidHom.mem_ker.mpr hq
    rw [hψker, hφker] at hl
    rw [hpck]
    exact hl
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.perfect
  haveI hPperf : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _)
  have hpctop : CFSG.pCore 2 ↥L ≠ ⊤ := by
    rw [hpck]
    intro htop
    exact hLnotV ((Subgroup.subgroupOf_eq_top).mp htop)
  haveI : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.nontrivial_iff.mpr hpctop
  have hnsolv : ¬ IsSolvable (↥L ⧸ CFSG.pCore 2 ↥L) := Group.IsPerfect.not_isSolvable _
  have hO2 : O2 (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) = ⊥ := by
    unfold O2
    rw [eq_bot_iff, iSup_le_iff]
    rintro ⟨N, -, hNnorm, hN2⟩
    have hNn : N.Normal := Subgroup.normalizer_eq_top_iff.mp (le_antisymm le_top hNnorm)
    let π : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
    have hker : IsPGroup 2 π.ker := by
      rw [QuotientGroup.ker_mk']
      exact CFSG.LieType.BorelTits.pCore_isPGroup 2
    have hpre : IsPGroup 2 (N.comap π) := IsPGroup.comap_of_ker_isPGroup hN2 π hker
    have hleN : N.comap π ≤ CFSG.pCore 2 ↥L := by
      unfold CFSG.pCore
      exact le_sSup ⟨hNn.comap π, hpre⟩
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) x
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L) y).mpr
      (hleN (Subgroup.mem_comap.mpr hx))
  have hno7 : ∀ {X : Type} [Group X] [Finite X]
      (f : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* X), 7 ∣ Nat.card X → False := by
    intro X _ _ f hdvd
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X) 7 hdvd
    have hgP : orderOf (f.symm g) = 7 := by
      rw [MulEquiv.orderOf_eq]
      exact hg
    obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) (f.symm g)
    have hn7 : n ^ 7 ∈ CFSG.pCore 2 ↥L := by
      refine (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L) (n ^ 7)).mp ?_
      rw [← QuotientGroup.mk'_apply, map_pow, hn, ← hgP]
      exact pow_orderOf_eq_one _
    have hn7V : (n : G) ^ 7 ∈ V := by
      have hmem := hn7
      rw [hpck] at hmem
      simpa using (Subgroup.mem_subgroupOf.mp hmem)
    have hcentral7 : ∀ v ∈ V, (n : G) ^ 7 * v * ((n : G) ^ 7)⁻¹ = v := by
      intro v hv
      have hcomm : (n : G) ^ 7 * v = v * (n : G) ^ 7 := by
        have hc := mul_comm' (⟨(n : G) ^ 7, hn7V⟩ : V) ⟨v, hv⟩
        exact congrArg Subtype.val hc
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hncent : (n : G) ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hnv : (n : G) * v = v * (n : G) := by
        have h1 := congrArg (fun x => x * (n : G))
          (h7 (n : G) (h.le_normalizer n.2) hcentral7 v hv)
        simpa [mul_assoc] using h1
      exact hnv.symm
    have hnV : (n : G) ∈ V := hC hncent
    have hnker : n ∈ CFSG.pCore 2 ↥L := by
      rw [hpck]
      exact Subgroup.mem_subgroupOf.mpr hnV
    have hg1 : f.symm g = 1 := by
      rw [← hn, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L) n).mpr hnker
    have hgone : g = 1 := by
      have := congrArg f hg1
      simpa using this
    rw [hgone] at hg
    simp at hg
  have hlist : CFSG.OddStandard.SmallF3.HarrisU33.Outside.GHII23List :=
    CFSG.OddStandard.SmallF3.HarrisU33.Outside.ghii23List_holds
  unfold CFSG.OddStandard.SmallF3.HarrisU33.Outside.GHII23List at hlist
  have hcases := hlist (↥L ⧸ CFSG.pCore 2 ↥L) ι hιinj hnsolv hO2
  refine ⟨hO, ?_⟩
  rcases hcases with h8 | h7a | h6p | h6 | hgl | h5p | h5 | hz3 | ⟨L', hidx, hL'⟩
  · obtain ⟨f⟩ := h8
    exact (hno7 f seven_dvd_card_alt_eight).elim
  · obtain ⟨f⟩ := h7a
    exact (hno7 f seven_dvd_card_alt_seven).elim
  · obtain ⟨f⟩ := h6p
    exact (CFSG.Quasithin.H13.L319.S66.not_isPerfect_of_mulEquiv_perm (m := 6) (by norm_num) f
      hPperf).elim
  · obtain ⟨f⟩ := h6
    exact Or.inl ⟨f⟩
  · obtain ⟨f⟩ := hgl
    exact (hno7 f seven_dvd_card_GL_three).elim
  · obtain ⟨f⟩ := h5p
    exact (CFSG.Quasithin.H13.L319.S66.not_isPerfect_of_mulEquiv_perm (m := 5) (by norm_num) f
      hPperf).elim
  · obtain ⟨f⟩ := h5
    exact Or.inr ⟨f⟩
  · obtain ⟨f⟩ := hz3
    exact (not_isPerfect_z3_mul_alt_five
      (Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective)).elim
  ·
    exfalso
    haveI : L'.Normal := Subgroup.normal_of_index_eq_two hidx
    have hcard : Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ L') = 2 := by
      rw [← Subgroup.index_eq_card]
      exact hidx
    haveI : IsCyclic ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ L') := isCyclic_of_prime_card hcard
    haveI : IsMulCommutative ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ L') := IsCyclic.isMulCommutative
    have hc : commutator (↥L ⧸ CFSG.pCore 2 ↥L) ≤ L' :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    rw [hPperf.commutator_eq_top, top_le_iff] at hc
    rw [hc, Subgroup.index_top] at hidx
    omega

end CFSG.SectionRank.QTK.Insp443

end
