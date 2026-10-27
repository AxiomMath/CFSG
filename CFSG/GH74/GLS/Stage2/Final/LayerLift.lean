module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.GH74.GLS.Stage2.Final.LayerLift

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

theorem mulAut_comm_of_cyclic (N : Type*) [Group N] [IsCyclic N] (a b : MulAut N) : a * b = b * a := by
  apply (IsCyclic.mulAutMulEquiv N).injective
  rw [map_mul, map_mul, mul_comm]

section Cent

variable {X : Type*} [Group X]

theorem commutatorElement_mem_centralizer_of_cyclic (N : Subgroup X) [N.Normal] [IsCyclic ↥N] (a b : X) :
    ⁅a, b⁆ ∈ centralizer (N : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have h : (MulAut.conjNormal ⁅a, b⁆ : MulAut ↥N) = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (mulAut_comm_of_cyclic ↥N (MulAut.conjNormal a) (MulAut.conjNormal b))
  have h1 := congrArg Subtype.val (DFunLike.congr_fun h ⟨n, hn⟩)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  have h2 : ⁅a, b⁆ * n = n * ⁅a, b⁆ := by
    calc ⁅a, b⁆ * n = (⁅a, b⁆ * n * ⁅a, b⁆⁻¹) * ⁅a, b⁆ := by group
      _ = n * ⁅a, b⁆ := by rw [h1]
  exact h2.symm

theorem le_centralizer_self_of_cyclic (N : Subgroup X) [IsCyclic ↥N] : N ≤ centralizer (N : Set X) := by
  intro n hn m hm
  let _ : CommGroup ↥N := IsCyclic.commGroup
  have h := mul_comm (⟨m, hm⟩ : ↥N) ⟨n, hn⟩
  exact congrArg Subtype.val h

theorem centralizes_of_perfect_quotient (N : Subgroup X) [N.Normal] [IsCyclic ↥N] (K : Subgroup X)
    (hperf : ⁅K.map (QuotientGroup.mk' N), K.map (QuotientGroup.mk' N)⁆ =
      K.map (QuotientGroup.mk' N)) {k : X} (hk : k ∈ K) {n : X} (hn : n ∈ N) : k * n = n * k := by
  have hcomm : ⁅K, K⁆ ≤ centralizer (N : Set X) :=
    Subgroup.commutator_le.mpr fun a _ b _ => commutatorElement_mem_centralizer_of_cyclic N a b
  have hk' : QuotientGroup.mk' N k ∈ ⁅K, K⁆.map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_commutator, hperf]
    exact Subgroup.mem_map_of_mem _ hk
  obtain ⟨c, hc, hck⟩ := hk'
  have hcn : c⁻¹ * k ∈ N := by
    rw [← QuotientGroup.eq]
    exact hck
  have hk2 : k = c * (c⁻¹ * k) := by group
  have h1 : c * n = n * c := (Subgroup.mem_centralizer_iff.mp (hcomm hc) n hn).symm
  have h2 : (c⁻¹ * k) * n = n * (c⁻¹ * k) :=
    (Subgroup.mem_centralizer_iff.mp (le_centralizer_self_of_cyclic N hcn) n hn).symm
  calc k * n = c * ((c⁻¹ * k) * n) := by rw [hk2]; group
    _ = c * (n * (c⁻¹ * k)) := by rw [h2]
    _ = (c * n) * (c⁻¹ * k) := by group
    _ = (n * c) * (c⁻¹ * k) := by rw [h1]
    _ = n * k := by group

end Cent

section Layer

variable {X : Type*} [Group X] [Finite X]

theorem map_layer_le_of_cyclic (N : Subgroup X) [N.Normal] [IsCyclic ↥N] :
    (layer X).map (QuotientGroup.mk' N) ≤ layer (X ⧸ N) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun J hJ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hnot : ¬ J ≤ (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    intro hle
    have hsolvN : Group.IsSolvable ↥N := inferInstance
    have hsolvJ : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
    have := hJ.1.1
    exact Group.IsPerfect.not_isSolvable ↥J hsolvJ
  exact CFSG.LocalCores.component_le_layer
    ⟨CFSG.LocalCores.isQuasisimple_map hJ.1 _ hnot, hJ.2.map (QuotientGroup.mk'_surjective _)⟩

omit [Finite X] in
theorem layer_quotient_le_map_of_cyclic (N : Subgroup X) [N.Normal] [IsCyclic ↥N] :
    layer (X ⧸ N) ≤ (layer X).map (QuotientGroup.mk' N) := by
  refine sSup_le fun Kb hKb => ?_
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπ
  set Kt : Subgroup X := Kb.comap π with hKt
  have hsub : Kt.IsSubnormal := hKb.2.comap π
  have hmap : Kt.map π = Kb := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Kb
  have hNKt : N ≤ Kt := by
    intro n hn
    show π n ∈ Kb
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  have hperfKb : ⁅Kb, Kb⁆ = Kb := Subgroup.isPerfect_iff.mp hKb.1.1
  have hperfKt : ⁅Kt.map π, Kt.map π⁆ = Kt.map π := by rw [hmap]; exact hperfKb
  have hcent : ∀ k ∈ Kt, ∀ n ∈ N, k * n = n * k := fun k hk n hn =>
    centralizes_of_perfect_quotient N Kt hperfKt hk hn
  let f : ↥Kt →* ↥Kb := π.subgroupComap Kb
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N (b : X ⧸ N)
    have hxKt : x ∈ Kt := by
      show π x ∈ Kb
      rw [hπ, hx]
      exact b.2
    exact ⟨⟨x, hxKt⟩, Subtype.ext hx⟩
  have hker : f.ker ≤ center ↥Kt := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : π (x : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxN : (x : X) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    exact Subtype.ext (hcent y.1 y.2 x hxN)
  have hq : IsQuasisimple ↥(commutator ↥Kt) :=
    CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective f hf hker hKb.1
  obtain ⟨-, -, hsurj⟩ := CFSG.LocalCores.central_extension_derived_of_surjective f hf hker hKb.1.1
  set K : Subgroup X := (commutator ↥Kt).map Kt.subtype with hK
  have hKle : K ≤ Kt := Subgroup.map_subtype_le _
  have hqK : IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((commutator ↥Kt).equivMapOfInjective Kt.subtype Kt.subtype_injective) hq
  have hKsn : K.IsSubnormal := by
    refine Subgroup.IsSubnormal.trans hKle ?_ hsub
    have h : K.subgroupOf Kt = commutator ↥Kt := by
      show Subgroup.comap Kt.subtype K = _
      rw [hK, Subgroup.comap_map_eq_self_of_injective Kt.subtype_injective]
    rw [h]
    exact Subgroup.Normal.isSubnormal inferInstance
  have hKlayer : K ≤ layer X := CFSG.LocalCores.component_le_layer ⟨hqK, hKsn⟩
  intro b hb
  obtain ⟨c, hc⟩ := hsurj ⟨b, hb⟩
  have hcK : ((c : ↥Kt) : X) ∈ K := ⟨(c : ↥Kt), c.2, rfl⟩
  exact ⟨((c : ↥Kt) : X), hKlayer hcK, congrArg Subtype.val hc⟩


theorem layer_map_quotient_of_cyclic (N : Subgroup X) [N.Normal] [IsCyclic ↥N] :
    (layer X).map (QuotientGroup.mk' N) = layer (X ⧸ N) :=
  le_antisymm (map_layer_le_of_cyclic N) (layer_quotient_le_map_of_cyclic N)

end Layer

section Cen

variable {G : Type} [Group G] [Finite G]

theorem barOf_layer_eq_of_cyclic (z : G) (hcyc : IsCyclic ↥(pPrimeCore 2 ↥(Cen z))) :
    barOf z ((layer ↥(Cen z)).map (Cen z).subtype) = layer (CentralizerBar z) := by
  have : IsCyclic ↥(pPrimeCore 2 ↥(Cen z)) := hcyc
  have h := layer_map_quotient_of_cyclic (pPrimeCore 2 ↥(Cen z))
  have hA : ((layer ↥(Cen z)).map (Cen z).subtype).subgroupOf (Cen z) = layer ↥(Cen z) := by
    show Subgroup.comap (Cen z).subtype _ = _
    exact Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective _
  unfold barOf
  rw [hA]
  exact h

theorem layerTimesSylow_inf_oddCore_eq_bot {z : G} {S : Subgroup G} (hS : IsPGroup 2 ↥S) (hSC : S ≤ Cen z)
    (hEC : (layer ↥(Cen z)).map (Cen z).subtype ⊓ OddCore z = ⊥) :
    layerTimesSylow z S ⊓ OddCore z = ⊥ := by
  classical
  set C : Subgroup G := Cen z with hC
  set E' : Subgroup ↥C := layer ↥C with hE'
  set S' : Subgroup ↥C := S.subgroupOf C with hS'
  set N' : Subgroup ↥C := pPrimeCore 2 ↥C with hN'
  have hchar : E'.Characteristic := CFSG.LocalCores.layer_characteristic
  have hnormE : E'.Normal := by
    haveI := hchar
    infer_instance
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxX, hxN⟩ := hx
  obtain ⟨n, hn, rfl⟩ := hxN
  have hmapS : S'.map C.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSC
  have hX : layerTimesSylow z S = (E' ⊔ S').map C.subtype := by
    unfold layerTimesSylow
    rw [Subgroup.map_sup, hmapS]
  rw [hX] at hxX
  obtain ⟨y, hy, hyn⟩ := hxX
  have hyn' : y = n := Subtype.ext hyn
  subst hyn'
  obtain ⟨e, he, s, hs, hes⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  have hodd : Odd (Nat.card ↥N') := by
    have := pPrimeCore_coprime_card (p := 2) (G := ↥C)
    exact (Nat.coprime_two_left.mp this)
  have hyN : (y ^ Nat.card ↥N') = 1 := by
    have h : (⟨y, hn⟩ : ↥N') ^ Nat.card ↥N' = 1 := pow_card_eq_one'
    have h2 := Subtype.ext_iff.mp h
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h2
    exact h2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS) ⟨(s : G), by
    have : (s : ↥C) ∈ S' := hs
    exact this⟩
  have hsk : (s ^ (2 ^ k)) = 1 := by
    have h := pow_orderOf_eq_one (⟨(s : G), by have : (s : ↥C) ∈ S' := hs; exact this⟩ : ↥S)
    rw [hk] at h
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  have h1 : (QuotientGroup.mk' E' y) = QuotientGroup.mk' E' s := by
    have he1 : QuotientGroup.mk' E' e = 1 := (QuotientGroup.eq_one_iff e).mpr he
    rw [← hes, map_mul, he1, one_mul]
  have h2 : orderOf (QuotientGroup.mk' E' y) ∣ Nat.card ↥N' := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hyN, map_one])
  have h3 : orderOf (QuotientGroup.mk' E' s) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hsk, map_one])
  rw [h1] at h2
  have hcop : Nat.Coprime (Nat.card ↥N') (2 ^ k) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
  have h4 : orderOf (QuotientGroup.mk' E' s) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h3
  have h5 : QuotientGroup.mk' E' s = 1 := orderOf_eq_one_iff.mp h4
  have hsE : s ∈ E' := (QuotientGroup.eq_one_iff s).mp h5
  have hyE : y ∈ E' := by rw [← hes]; exact E'.mul_mem he hsE
  have hmem : (y : G) ∈ (layer ↥(Cen z)).map (Cen z).subtype ⊓ OddCore z :=
    ⟨⟨y, hyE, rfl⟩, ⟨y, hn, rfl⟩⟩
  rw [hEC] at hmem
  exact hmem

end Cen

end CFSG.GH74.GLS.Stage2.Final.LayerLift
