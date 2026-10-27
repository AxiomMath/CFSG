module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.ConeTopGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Step
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Quat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.LayerBalanceAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ComponentOrder
public import CFSG.Dihedral.BrauerSuzuki
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Sylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

theorem exists_central_involution_of_pRank_one {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hr : CFSG.pRank 2 X = 1) :
    ∃ t : X, t ∈ center X ∧ orderOf t = 2 := by
  have hP2 := hq.2.2
  let P : Sylow 2 X := default
  let π : X →* X ⧸ center X := QuotientGroup.mk' (center X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have : IsSimpleGroup (X ⧸ center X) := hq.2.1
  rcases Junction.sylow_cyclic_or_quaternion hr P with hcyc | ⟨e, he, ⟨eQ⟩⟩
  · exfalso
    let P' : Sylow 2 (X ⧸ center X) := Sylow.mapSurjective hπ P
    have hP' : (P' : Subgroup (X ⧸ center X)) = (P : Subgroup X).map π :=
      Sylow.coe_mapSurjective hπ P
    let gP : ↥(P : Subgroup X) →* ↥(P' : Subgroup (X ⧸ center X)) :=
      (π.comp (P : Subgroup X).subtype).codRestrict _ (fun x => hP' ▸ ⟨x, x.2, rfl⟩)
    have hgP : Function.Surjective gP := by
      rintro ⟨y, hy⟩
      rw [hP'] at hy
      obtain ⟨p, hp, rfl⟩ := hy
      exact ⟨⟨p, hp⟩, rfl⟩
    have : IsCyclic ↥(P' : Subgroup (X ⧸ center X)) := isCyclic_of_surjective gP hgP
    exact Junction.not_isCyclic_sylow_two hP2 P' this
  · have hm : NeZero (2 ^ e) := ⟨by positivity⟩
    set m : ℕ := 2 ^ e with hmdef
    have hm2 : 2 ≤ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    have hsq : (QuaternionGroup.a (m : ZMod (2 * m)) : QuaternionGroup m) ^ 2 = 1 := by
      rw [pow_two, QuaternionGroup.a_mul_a, QuaternionGroup.one_def]
      congr 1
      simpa only [two_mul, Nat.cast_add] using ZMod.natCast_self (2 * m)
    have hne1 : (QuaternionGroup.a (m : ZMod (2 * m)) : QuaternionGroup m) ≠ 1 := by
      intro h
      rw [QuaternionGroup.one_def, QuaternionGroup.a.injEq] at h
      have h1 := (ZMod.natCast_eq_zero_iff m (2 * m)).1 h
      have := Nat.le_of_dvd (by omega) h1
      omega
    have hord : orderOf (QuaternionGroup.a (m : ZMod (2 * m)) : QuaternionGroup m) = 2 :=
      orderOf_eq_prime hsq hne1
    set t : X := ((eQ (QuaternionGroup.a (m : ZMod (2 * m))) : ↥(P : Subgroup X)) : X) with ht
    have htP : t ∈ (P : Subgroup X) := (eQ (QuaternionGroup.a (m : ZMod (2 * m)))).2
    have htord : orderOf t = 2 := by
      rw [ht, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hord]
    have hquat : Nonempty ((P : Subgroup X) ≃* QuaternionGroup (2 ^ (e + 2 - 2))) := by
      rw [Nat.add_sub_cancel]
      exact ⟨eQ.symm⟩
    have hBS := CFSG.BrauerSuzuki.brauer_suzuki (e + 2) (by omega) P hquat t htP htord
    exact ⟨t, Junction.mem_center_of_mk_mem_center_oddCore hq hBS, htord⟩

section Orbit

variable {G : Type} [Group G]

theorem layerIn_map_conj_le {D : Subgroup G} {g : G} (hg : g ∈ D) :
    (layerIn D).map (MulAut.conj g).toMonoidHom ≤ layerIn D := by
  rw [Subgroup.map_le_iff_le_comap]
  refine Junction.layerIn_le_iff.2 fun Z hZ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact Junction.le_layerIn_of_isCompIn (hZ.map_conj hg)

theorem map_conj_conjClosure_le {L S : Subgroup G} {g : G} (hL : ∀ x ∈ L, g * x = x * g)
    (hS : S.map (MulAut.conj g).toMonoidHom ≤ S) :
    (conjClosure L S).map (MulAut.conj g).toMonoidHom ≤ conjClosure L S := by
  rw [conjClosure, Subgroup.map_iSup]
  refine iSup_le fun l => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hl => ?_
  have hl' : g * l * g⁻¹ ∈ S := hS ⟨l, hl, by simp [MulAut.conj_apply]⟩
  rw [Induction.map_conj_map_conj]
  refine le_trans ?_ (Junction.map_conj_le_conjClosure (L := L) hl')
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, hx, ?_⟩
  have hx' : g⁻¹ * x * g = x := by
    calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
      _ = g⁻¹ * (g * x) := by rw [hL x hx]
      _ = x := by group
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * l * g⁻¹ * x * (g * l * g⁻¹)⁻¹ = g * l * (g⁻¹ * x * g) * l⁻¹ * g⁻¹ := by group
    _ = g * l * x * l⁻¹ * g⁻¹ := by rw [hx']
    _ = _ := by group

variable [Finite G]

theorem eq_or_eq_of_isCompIn_le_sup {D M₁ M₂ W : Subgroup G} (h₁ : IsCompIn M₁ D)
    (h₂ : IsCompIn M₂ D) (hne : M₁ ≠ M₂) (hW : IsCompIn W D) (hle : W ≤ M₁ ⊔ M₂) :
    W = M₁ ∨ W = M₂ := by
  by_contra hcon
  push Not at hcon
  have c₁ := hW.commute_of_ne h₁ hcon.1
  have c₂ := hW.commute_of_ne h₂ hcon.2
  refine not_forall_commute_of_isQuasisimple hW.isQuasisimple fun a ha b hb => ?_
  have hW1 : W ≤ centralizer (M₁ : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun x hx => (c₁ a ha x hx).symm
  have hW2 : W ≤ centralizer (M₂ : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun x hx => (c₂ a ha x hx).symm
  have := Junction.le_centralizer_sup hW1 hW2 ha
  exact (mem_centralizer_iff.1 this b (hle hb)).symm

theorem map_conj_eq_or_eq_of_map_conj_sup_le {D M M' W : Subgroup G} {g : G}
    (hM : IsCompIn M D) (hM' : IsCompIn M' D) (hne : M ≠ M') (hg : g ∈ D)
    (hstab : (M ⊔ M').map (MulAut.conj g).toMonoidHom ≤ M ⊔ M') (hW : W = M ∨ W = M') :
    W.map (MulAut.conj g).toMonoidHom = M ∨ W.map (MulAut.conj g).toMonoidHom = M' := by
  have hWc : IsCompIn W D := by rcases hW with rfl | rfl; exacts [hM, hM']
  have hWle : W ≤ M ⊔ M' := by rcases hW with rfl | rfl; exacts [le_sup_left, le_sup_right]
  exact eq_or_eq_of_isCompIn_le_sup hM hM' hne (hWc.map_conj hg)
    ((Subgroup.map_mono hWle).trans hstab)

theorem card_le_two_mul_card_inf_normalizer_of_map_conj {S M M' : Subgroup G}
    (hperm : ∀ g ∈ S, M.map (MulAut.conj g).toMonoidHom = M ∨
      M.map (MulAut.conj g).toMonoidHom = M') :
    Nat.card S ≤ 2 * Nat.card (S ⊓ normalizer (M : Set G) : Subgroup G) := by
  have hmapM : ∀ a : G, a ∈ S → a ∉ (S ⊓ normalizer (M : Set G) : Subgroup G) →
      M.map (MulAut.conj a).toMonoidHom = M' := by
    intro a ha hanot
    rcases hperm a ha with h | h
    · exact absurd ⟨ha, Solomon78.mem_normalizer_iff_map_conj_eq.2 h⟩ hanot
    · exact h
  refine card_le_two_mul_card_of_inv_mul_mem inf_le_left fun a ha b hb hanot hbnot => ?_
  have hab : M.map (MulAut.conj (a⁻¹ * b)).toMonoidHom = M := by
    rw [← Induction.map_conj_map_conj M b a⁻¹, hmapM b hb hbnot, ← hmapM a ha hanot,
      Induction.map_conj_map_conj, inv_mul_cancel]
    ext x
    simp [MulAut.conj_apply]
  exact ⟨S.mul_mem (S.inv_mem ha) hb, Solomon78.mem_normalizer_iff_map_conj_eq.2 hab⟩

theorem mul_conj_mem_of_ltF_ne {K L : Subgroup G} {s t : G} (hs : orderOf s = 2)
    (hst : s * t = t * s) (hK : IsCompIn K (centralizer ({s} : Set G)))
    (hL : IsCompIn L (centralizer ({t} : Set G)))
    (hKL : K ≤ L ⊔ L.map (MulAut.conj s).toMonoidHom)
    (hne : L.map (MulAut.conj s).toMonoidHom ≠ L) :
    ∀ m ∈ L, m * (s * m * s⁻¹) ∈ K := by
  have hc := Zassenhaus.commute_conj_of_ne hst hL hne
  have hss : s * s = 1 := Zassenhaus.mul_self_eq_one_of_orderOf_eq_two hs
  have hsq : ∀ a ∈ L, s * s * a = a * (s * s) := fun a _ => by rw [hss]; simp
  set φ := Zassenhaus.foldHom s L hc with hφ
  have hker : φ.ker ≤ center ↥L := foldHom_ker_le_center hc
  have hR : CFSG.IsQuasisimple ↥φ.range :=
    Zassenhaus.isQuasisimple_range_of_ker_le_center hL.isQuasisimple φ hker
  have hRs : φ.range ≤ centralizer ({s} : Set G) := range_foldHom_le_centralizer_of_sq hsq hc
  have hKR : K ≤ φ.range :=
    Zassenhaus.le_range_foldHom hss hc (fun _ hx => hK.le hx) hK.isQuasisimple.1 hKL
  have hsub : (K.subgroupOf φ.range).IsSubnormal :=
    Zassenhaus.isSubnormal_subgroupOf_of_le hRs hK.2.2
  have hKeq : K = φ.range :=
    Step.eq_of_le_of_isSubnormal_of_isQuasisimple hKR hK.isQuasisimple hR hsub
  intro m hm
  rw [hKeq]
  exact ⟨⟨m, hm⟩, rfl⟩

theorem commute_of_fixes_mul_conj {M : Subgroup G} {s p : G} (hperf : ⁅M, M⁆ = M)
    (hc : ∀ a ∈ M, ∀ b ∈ M.map (MulAut.conj s).toMonoidHom, a * b = b * a)
    (hpM : p ∈ normalizer (M : Set G))
    (hpM' : p ∈ normalizer (M.map (MulAut.conj s).toMonoidHom : Set G))
    (hfix : ∀ m ∈ M, p * (m * (s * m * s⁻¹)) = (m * (s * m * s⁻¹)) * p) :
    (∀ m ∈ M, p * m = m * p) ∧ ∀ m ∈ M, p * (s * m * s⁻¹) = (s * m * s⁻¹) * p := by
  set M' := M.map (MulAut.conj s).toMonoidHom with hM'
  have hm' : ∀ m ∈ M, s * m * s⁻¹ ∈ M' := fun m hm => ⟨m, hm, by simp [MulAut.conj_apply]⟩
  have hψ : ∀ m ∈ M, m⁻¹ * (p * m * p⁻¹) ∈ M ∧ m⁻¹ * (p * m * p⁻¹) ∈ M' := by
    intro m hm
    have h1 : p * m * p⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.1 hpM m).1 hm
    have h2 : p * (s * m * s⁻¹) * p⁻¹ ∈ M' :=
      (Subgroup.mem_normalizer_iff.1 hpM' _).1 (hm' m hm)
    refine ⟨M.mul_mem (M.inv_mem hm) h1, ?_⟩
    have h3 : p * (m * (s * m * s⁻¹)) * p⁻¹ = m * (s * m * s⁻¹) := by
      rw [hfix m hm]; group
    have h4 : m⁻¹ * (p * m * p⁻¹) = (s * m * s⁻¹) * (p * (s * m * s⁻¹) * p⁻¹)⁻¹ := by
      have : p * (m * (s * m * s⁻¹)) * p⁻¹ = (p * m * p⁻¹) * (p * (s * m * s⁻¹) * p⁻¹) := by group
      rw [this] at h3
      calc m⁻¹ * (p * m * p⁻¹) = m⁻¹ * ((p * m * p⁻¹) * (p * (s * m * s⁻¹) * p⁻¹)) *
            (p * (s * m * s⁻¹) * p⁻¹)⁻¹ := by group
        _ = m⁻¹ * (m * (s * m * s⁻¹)) * (p * (s * m * s⁻¹) * p⁻¹)⁻¹ := by rw [h3]
        _ = _ := by group
    rw [h4]
    exact M'.mul_mem (hm' m hm) (M'.inv_mem h2)
  let ψ : ↥M →* G := MonoidHom.mk' (fun m : ↥M => (m : G)⁻¹ * (p * (m : G) * p⁻¹)) (by
    intro m n
    have hψm := (hψ m m.2).2
    have hcn : (n : G)⁻¹ * (m : G)⁻¹ * (p * (m : G) * p⁻¹) =
        (m : G)⁻¹ * (p * (m : G) * p⁻¹) * (n : G)⁻¹ := by
      have := hc _ (M.inv_mem n.2) _ hψm
      calc (n : G)⁻¹ * (m : G)⁻¹ * (p * (m : G) * p⁻¹)
          = (n : G)⁻¹ * ((m : G)⁻¹ * (p * (m : G) * p⁻¹)) := by group
        _ = (m : G)⁻¹ * (p * (m : G) * p⁻¹) * (n : G)⁻¹ := this
    simp only [Subgroup.coe_mul, mul_inv_rev]
    calc (n : G)⁻¹ * (m : G)⁻¹ * (p * ((m : G) * n) * p⁻¹)
        = ((n : G)⁻¹ * (m : G)⁻¹ * (p * (m : G) * p⁻¹)) * (p * n * p⁻¹) := by group
      _ = ((m : G)⁻¹ * (p * (m : G) * p⁻¹) * (n : G)⁻¹) * (p * n * p⁻¹) := by rw [hcn]
      _ = _ := by group)
  have hψ1 : ∀ m : ↥M, ψ m = 1 := by
    haveI : Group.IsPerfect ↥M := Subgroup.isPerfect_iff.2 hperf
    refine map_eq_one_of_isPerfect_of_commute ψ (fun x y => ?_)
    show (x : G)⁻¹ * (p * (x : G) * p⁻¹) * ((y : G)⁻¹ * (p * (y : G) * p⁻¹)) =
      (y : G)⁻¹ * (p * (y : G) * p⁻¹) * ((x : G)⁻¹ * (p * (x : G) * p⁻¹))
    exact (hc _ (hψ y y.2).1 _ (hψ x x.2).2).symm
  have hcomm : ∀ m ∈ M, p * m = m * p := by
    intro m hm
    have := hψ1 ⟨m, hm⟩
    have h5 : (m : G)⁻¹ * (p * m * p⁻¹) = 1 := this
    calc p * m = m * (m⁻¹ * (p * m * p⁻¹)) * p := by group
      _ = m * p := by rw [h5]; group
  refine ⟨hcomm, fun m hm => ?_⟩
  have h6 := hfix m hm
  have h7 := hcomm m hm
  have h8 : p * (m * (s * m * s⁻¹)) = m * (p * (s * m * s⁻¹)) := by
    calc p * (m * (s * m * s⁻¹)) = (p * m) * (s * m * s⁻¹) := by group
      _ = (m * p) * (s * m * s⁻¹) := by rw [h7]
      _ = m * (p * (s * m * s⁻¹)) := by group
  have h9 : m * (p * (s * m * s⁻¹)) = m * ((s * m * s⁻¹) * p) := by
    calc m * (p * (s * m * s⁻¹)) = p * (m * (s * m * s⁻¹)) := h8.symm
      _ = (m * (s * m * s⁻¹)) * p := h6
      _ = m * ((s * m * s⁻¹) * p) := by group
  exact mul_left_cancel h9

theorem two_mul_card_le_of_diagonal {X M S : Subgroup G} {s z : G}
    (hs : orderOf s = 2) (hsz : s * z = z * s)
    (hXs : IsCompIn X (centralizer ({s} : Set G))) (hzX : z ∈ X)
    (hM : IsCompIn M (centralizer ({z} : Set G)))
    (hne : M.map (MulAut.conj s).toMonoidHom ≠ M)
    (hXM : X ≤ M ⊔ M.map (MulAut.conj s).toMonoidHom)
    (hcl : M ⊔ M.map (MulAut.conj s).toMonoidHom =
      conjClosure X (layerIn (centralizer ({z} : Set G))))
    (hS : IsPGroup 2 S) (hSX : S ≤ centralizer (X : Set G)) :
    2 * Nat.card S ≤ 2 ^ (Nat.card (centralizer (M : Set G))).factorization 2 := by
  set D := centralizer ({z} : Set G) with hD
  set M' := M.map (MulAut.conj s).toMonoidHom with hM'
  have hMs : IsCompIn M' D := Zassenhaus.isCompIn_conj_of_commute hsz hM
  have hc : ∀ a ∈ M, ∀ b ∈ M', a * b = b * a := Zassenhaus.commute_conj_of_ne hsz hM hne
  have hSD : ∀ g ∈ S, g ∈ D := fun g hg =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hSX hg) z hzX).symm
  have hSX' : ∀ g ∈ S, ∀ x ∈ X, g * x = x * g := fun g hg x hx =>
    (mem_centralizer_iff.1 (hSX hg) x hx).symm
  have hPS : ∀ g ∈ S, (M ⊔ M').map (MulAut.conj g).toMonoidHom ≤ M ⊔ M' := by
    intro g hg
    rw [hcl]
    exact map_conj_conjClosure_le (hSX' g hg) (layerIn_map_conj_le (hSD g hg))
  have hperm : ∀ g ∈ S, ∀ W, (W = M ∨ W = M') →
      W.map (MulAut.conj g).toMonoidHom = M ∨ W.map (MulAut.conj g).toMonoidHom = M' :=
    fun g hg W hW =>
      map_conj_eq_or_eq_of_map_conj_sup_le hM hMs (Ne.symm hne) (hSD g hg) (hPS g hg) hW
  set N := S ⊓ normalizer (M : Set G) with hN
  have hindex : Nat.card S ≤ 2 * Nat.card N :=
    card_le_two_mul_card_inf_normalizer_of_map_conj fun g hg => hperm g hg M (Or.inl rfl)
  set C := S ⊓ centralizer (M : Set G) ⊓ centralizer (M' : Set G) with hC
  have hNC : N ≤ C := by
    intro p hp
    obtain ⟨hpS, hpM⟩ := hp
    have hpM_eq : M.map (MulAut.conj p).toMonoidHom = M :=
      Solomon78.mem_normalizer_iff_map_conj_eq.1 hpM
    have hpM' : M'.map (MulAut.conj p).toMonoidHom = M' := by
      rcases hperm p hpS M' (Or.inr rfl) with h | h
      · exfalso
        apply hne
        exact Subgroup.map_injective (MulEquiv.injective (MulAut.conj p)) (h.trans hpM_eq.symm)
      · exact h
    have hfix : ∀ m ∈ M, p * (m * (s * m * s⁻¹)) = (m * (s * m * s⁻¹)) * p := fun m hm =>
      hSX' p hpS _ (mul_conj_mem_of_ltF_ne hs hsz hXs hM hXM hne m hm)
    obtain ⟨h1, h2⟩ := commute_of_fixes_mul_conj (Subgroup.isPerfect_iff.1 hM.isQuasisimple.1)
      hc hpM (Solomon78.mem_normalizer_iff_map_conj_eq.2 hpM') hfix
    refine ⟨⟨hpS, mem_centralizer_iff.2 fun m hm => (h1 m hm).symm⟩, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (h2 m hm).symm
  have hcard : 4 * Nat.card C ≤ 2 ^ (Nat.card (centralizer (M : Set G))).factorization 2 := by
    refine four_mul_card_le_of_isQuasisimple (A := M) (B := M') (C := C) hMs.isQuasisimple
      (fun b hb a ha => (hc a ha b hb).symm) (hS.to_le (inf_le_left.trans inf_le_left)) ?_ ?_
    · intro c hc' a ha
      exact (mem_centralizer_iff.1 hc'.1.2 a ha).symm
    · intro c hc' b hb
      exact (mem_centralizer_iff.1 hc'.2 b hb).symm
  have := Subgroup.card_le_of_le hNC
  omega

end Orbit

variable {G : Type} [Group G] [Finite G]

theorem exists_coneTop {K : Subgroup G} (hK : InLF K) :
    ∃ X : Subgroup G, (X = K ∨ TransGen LtF K X) ∧ MaximalF X ∧
      (∀ Y, TransGen LtF K Y → Nat.card Y ≤ Nat.card X) ∧
      (∀ Y, TransGen LtF K Y → Nat.card Y = Nat.card X →
        (Nat.card (centralizer (Y : Set G))).factorization 2 ≤
          (Nat.card (centralizer (X : Set G))).factorization 2) := by
  set 𝒴 : Set (Subgroup G) := {Y | Y = K ∨ TransGen LtF K Y} with h𝒴
  obtain ⟨X₁, hX₁, hmax₁⟩ := Set.exists_max_image 𝒴 (fun Y => Nat.card Y) (Set.toFinite _)
    ⟨K, Or.inl rfl⟩
  set 𝒴' : Set (Subgroup G) := {Y | Y ∈ 𝒴 ∧ Nat.card Y = Nat.card X₁} with h𝒴'
  obtain ⟨X, ⟨hX, hXc⟩, hmax₂⟩ := Set.exists_max_image 𝒴'
    (fun Y => (Nat.card (centralizer (Y : Set G))).factorization 2) (Set.toFinite _)
    ⟨X₁, hX₁, rfl⟩
  have hup : ∀ Y, TransGen LtF K Y → Nat.card Y ≤ Nat.card X := fun Y hY =>
    hXc ▸ hmax₁ Y (Or.inr hY)
  have hXtrans : ∀ L, TransGen LtF X L → TransGen LtF K L := by
    intro L hL
    rcases hX with rfl | hX
    · exact hL
    · exact hX.trans hL
  refine ⟨X, hX, ⟨?_, fun L hL => ?_⟩, hup, fun Y hY hYc => hmax₂ Y ⟨Or.inr hY, hYc.trans hXc⟩⟩
  · rcases hX with rfl | hX
    · exact hK
    · exact Zassenhaus.inLF_right_of_transGen_ltF hX
  · obtain ⟨h1, h2⟩ := Zassenhaus.card_le_of_transGen_ltF hL
    exact h2 (le_antisymm (hup L (hXtrans L hL)) h1).symm

theorem isCompIn_of_coneTop_rankOne (h15 : FS79Lemma15At G)
    (hKp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (hO : CFSG.oddCore G = ⊥)
    {K X : Subgroup G} (hK : InLF K) (hXK : X = K ∨ TransGen LtF K X)
    (hmax1 : ∀ Y, TransGen LtF K Y → Nat.card Y ≤ Nat.card X)
    (hmax2 : ∀ Y, TransGen LtF K Y → Nat.card Y = Nat.card X →
      (Nat.card (centralizer (Y : Set G))).factorization 2 ≤
        (Nat.card (centralizer (X : Set G))).factorization 2)
    (hrk : CFSG.pRank 2 ↥X = 1) :
    ∃ z ∈ X, orderOf z = 2 ∧ IsCompIn X (centralizer ({z} : Set G)) := by
  have hX : InLF X := by
    rcases hXK with rfl | h
    · exact hK
    · exact Zassenhaus.inLF_right_of_transGen_ltF h
  obtain ⟨s, hs, hXs⟩ := hX
  obtain ⟨zX, hzXc, hzX2⟩ := exists_central_involution_of_pRank_one hXs.isQuasisimple hrk
  set z : G := (zX : G) with hz
  have hzmem : z ∈ X := zX.2
  have hz2 : orderOf z = 2 := by rw [hz, Subgroup.orderOf_coe]; exact hzX2
  have hzc : ∀ x ∈ X, z * x = x * z := fun x hx => by
    have := Subgroup.mem_center_iff.1 hzXc ⟨x, hx⟩
    exact (congrArg Subtype.val this).symm
  have hsz : s * z = z * s := (mem_centralizer_singleton_iff.1 (hXs.le hzmem)).symm
  have hsX : ∀ x ∈ X, s * x = x * s := fun x hx =>
    (mem_centralizer_singleton_iff.1 (hXs.le hx)).symm
  have hT : IsPGroup 2 ↥(zpowers s ⊔ zpowers z) :=
    isPGroup_sup_zpowers (isPGroup_zpowers_of_orderOf_two hs)
      (Junction.mem_normalizer_zpowers_of_commute hsz.symm)
      (by rw [pow_two, Zassenhaus.mul_self_eq_one_of_orderOf_eq_two hz2]; exact one_mem _)
  have hTX : zpowers s ⊔ zpowers z ≤ centralizer (X : Set G) := by
    refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
    · exact mem_centralizer_iff.2 fun x hx => (hsX x hx).symm
    · exact mem_centralizer_iff.2 fun x hx => (hzc x hx).symm
  obtain ⟨S, hTS, hSX, hSp, hScard⟩ := exists_isPGroup_card_eq hT hTX
  have hsS : s ∈ S := hTS (le_sup_left (a := zpowers s) (b := zpowers z) (mem_zpowers s))
  have hzS : z ∈ S := hTS (le_sup_right (a := zpowers s) (b := zpowers z) (mem_zpowers z))
  have hSX' : ∀ g ∈ S, ∀ x ∈ X, g * x = x * g := fun g hg x hx =>
    (mem_centralizer_iff.1 (hSX hg) x hx).symm
  have hXS : IsCompIn X (centralizer (S : Set G)) :=
    isCompIn_of_le hXs (fun x hx => mem_centralizer_iff.2 fun g hg => hSX' g hg x hx)
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hsS))
  have hbal : X ≤ layerIn (centralizer ((zpowers z : Subgroup G) : Set G)) :=
    Junction.layerBalanceKAt_of_lemma15At h15 hKp hO S z hSp hz2 hzS
      (fun g hg => hSX' g hg z hzmem) X hXS
  have hu : s ∈ normalizer ((zpowers z : Subgroup G) : Set G) :=
    Junction.mem_normalizer_zpowers_of_commute hsz
  have hu2 : s ^ 2 ∈ zpowers z := by
    rw [pow_two, Zassenhaus.mul_self_eq_one_of_orderOf_eq_two hs]
    exact one_mem _
  have hKc : IsCompIn X (centralizer ((zpowers z ⊔ zpowers s : Subgroup G) : Set G)) := by
    refine isCompIn_of_le hXs ?_ ?_
    · rw [Step.centralizer_sup_zpowers, centralizer_zpowers_eq]
      exact le_inf (fun x hx => mem_centralizer_singleton_iff.2 (hzc x hx).symm) hXs.le
    · rw [Step.centralizer_sup_zpowers]
      exact inf_le_right
  rcases pumpUp_trichotomy hu hu2 hKc hbal with hcomp | ⟨M, hM, hMX, hlink, hXle, hcl⟩
  · refine ⟨z, hzmem, hz2, ?_⟩
    rwa [centralizer_zpowers_eq] at hcomp
  · exfalso
    rw [centralizer_zpowers_eq] at hM hcl
    have hlt : LtF X M := ⟨s, z, hs, hz2, hsz, hXs, hM, hXle⟩
    have hcone : TransGen LtF K M := by
      rcases hXK with rfl | h
      · exact TransGen.single hlt
      · exact h.tail hlt
    have hMX' : Nat.card M ≤ Nat.card X := hmax1 M hcone
    obtain ⟨hXM_le, -⟩ := Zassenhaus.card_le_of_ltF hlt
    rcases hlink with hvert | ⟨hne', -⟩
    · have hXM : X ≤ M := Zassenhaus.le_of_conj_eq hvert.symm hXle
      exact hMX (Subgroup.eq_of_le_of_card_ge hXM hMX').symm
    · have hcard : Nat.card M = Nat.card X := le_antisymm hMX' hXM_le
      have h2 := hmax2 M hcone hcard
      have hcount := two_mul_card_le_of_diagonal hs hsz hXs hzmem hM (Ne.symm hne') hXle hcl
        hSp hSX
      rw [hScard] at hcount
      have h3 : 2 ^ (Nat.card (centralizer (M : Set G))).factorization 2 ≤
          2 ^ (Nat.card (centralizer (X : Set G))).factorization 2 :=
        Nat.pow_le_pow_right (by norm_num) h2
      have h5 : 0 < 2 ^ (Nat.card (centralizer (X : Set G))).factorization 2 := by positivity
      omega

end CFSG.EvenSporadicStandard.M12Std.Rbc
