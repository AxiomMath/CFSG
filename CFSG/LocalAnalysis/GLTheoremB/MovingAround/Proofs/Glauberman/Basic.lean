module

public import CFSG.GH74.GLS.Stage2.Signalizer.L53Embed
public import CFSG.GH74.GLS.Stage2.Signalizer.L53Chief

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

open Subgroup
open CFSG.GH74.GLS.Bg (kLowInfty)
open CFSG.GH74.GLS.Stage2.Signalizer.L53 (IsChiefPair)
open scoped commutatorElement

section IterComm

variable {G : Type*} [Group G]

@[expose] def iterComm (x g : G) (n : ℕ) : G := (fun y => ⁅y, g⁆)^[n] x

theorem iterComm_zero (x g : G) : iterComm x g 0 = x := rfl

theorem iterComm_succ (x g : G) (n : ℕ) : iterComm x g (n + 1) = ⁅iterComm x g n, g⁆ :=
  Function.iterate_succ_apply' _ n x

theorem iterComm_succ' (x g : G) (n : ℕ) : iterComm x g (n + 1) = iterComm ⁅x, g⁆ g n :=
  Function.iterate_succ_apply _ n x

theorem iterComm_add (x g : G) (m n : ℕ) : iterComm x g (m + n) = iterComm (iterComm x g m) g n := by
  unfold iterComm
  rw [add_comm, Function.iterate_add_apply]

theorem iterComm_one (g : G) (n : ℕ) : iterComm 1 g n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterComm_succ, ih, commutatorElement_one_left]

theorem comm_mem_of_normal {N : Subgroup G} (hN : N.Normal) {x : G} (hx : x ∈ N) (g : G) :
    ⁅x, g⁆ ∈ N := by
  have e : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact N.mul_mem hx (hN.conj_mem _ (N.inv_mem hx) g)

theorem iterComm_mem {N : Subgroup G} (hN : N.Normal) {x : G} (hx : x ∈ N) (g : G) (n : ℕ) :
    iterComm x g n ∈ N := by
  induction n with
  | zero => exact hx
  | succ n ih => rw [iterComm_succ]; exact comm_mem_of_normal hN ih g

theorem iterComm_mem_of_le {N : Subgroup G} (hN : N.Normal) {x g : G} {m n : ℕ}
    (h : iterComm x g m ∈ N) (hmn : m ≤ n) : iterComm x g n ∈ N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [iterComm_add]
  exact iterComm_mem hN h g k

theorem iterComm_mul_right {V : Subgroup G} (hV : V.Normal) (x : G) {v : G} (hv : v ∈ V) (g : G)
    (n : ℕ) : ∃ w ∈ V, iterComm (x * v) g n = iterComm x g n * w := by
  induction n with
  | zero => exact ⟨v, hv, rfl⟩
  | succ n ih =>
    obtain ⟨w, hw, e⟩ := ih
    refine ⟨(g * iterComm x g n) * (g⁻¹ * w * g * w⁻¹) * (g * iterComm x g n)⁻¹, ?_, ?_⟩
    · refine hV.conj_mem _ (V.mul_mem ?_ (V.inv_mem hw)) _
      have := hV.conj_mem w hw g⁻¹
      rwa [inv_inv] at this
    · rw [iterComm_succ, iterComm_succ, e]
      simp only [commutatorElement_def]
      group

theorem iterComm_mul_mem_iff {V : Subgroup G} (hV : V.Normal) (x : G) {v : G} (hv : v ∈ V)
    (g : G) (n : ℕ) : iterComm (x * v) g n ∈ V ↔ iterComm x g n ∈ V := by
  obtain ⟨w, hw, e⟩ := iterComm_mul_right hV x hv g n
  rw [e]
  exact ⟨fun h => by simpa using V.mul_mem h (V.inv_mem hw), fun h => V.mul_mem h hw⟩

theorem map_iterComm {G' : Type*} [Group G'] (f : G →* G') (x g : G) (n : ℕ) :
    f (iterComm x g n) = iterComm (f x) (f g) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterComm_succ, iterComm_succ, map_commutatorElement, ih]

theorem conj_iterComm (c x g : G) (n : ℕ) :
    c * iterComm x g n * c⁻¹ = iterComm (c * x * c⁻¹) (c * g * c⁻¹) n := by
  have := map_iterComm (MulAut.conj c).toMonoidHom x g n
  simpa [MulAut.conj_apply] using this

end IterComm

section Sylow

variable {G : Type*} [Group G] {p : ℕ}

@[expose] def IsSylowOf (p : ℕ) (H T : Subgroup G) : Prop :=
  T ≤ H ∧ IsPGroup p T ∧ ¬ p ∣ T.relIndex H

theorem IsSylowOf.of_sylow [Fact p.Prime] [Finite G] (S : Sylow p G) {H : Subgroup G}
    (hSH : (S : Subgroup G) ≤ H) : IsSylowOf p H S :=
  ⟨hSH, S.isPGroup', fun h => S.not_dvd_index (h.trans (relIndex_dvd_index_of_le hSH))⟩

theorem IsSylowOf.top [Fact p.Prime] [Finite G] (S : Sylow p G) : IsSylowOf p ⊤ (S : Subgroup G) :=
  IsSylowOf.of_sylow S le_top

theorem IsSylowOf.mono {H H' T : Subgroup G} (h : IsSylowOf p H T) (hTH' : T ≤ H')
    (hH'H : H' ≤ H) : IsSylowOf p H' T := by
  refine ⟨hTH', h.2.1, fun hd => h.2.2 ?_⟩
  rw [← relIndex_mul_relIndex T H' H hTH' hH'H]
  exact hd.mul_right _

theorem IsSylowOf.isPGroup_subgroupOf {H T : Subgroup G} (h : IsSylowOf p H T) :
    IsPGroup p ↥(T.subgroupOf H) :=
  h.2.1.comap_subtype

@[expose] noncomputable def IsSylowOf.toSylow [Fact p.Prime] {H T : Subgroup G}
    (h : IsSylowOf p H T) : Sylow p ↥H :=
  h.isPGroup_subgroupOf.toSylow h.2.2

@[simp] theorem IsSylowOf.coe_toSylow [Fact p.Prime] {H T : Subgroup G} (h : IsSylowOf p H T) :
    (h.toSylow : Subgroup ↥H) = T.subgroupOf H :=
  IsPGroup.toSylow_coe _ _

theorem map_subgroupOf_eq {H T : Subgroup G} (hTH : T ≤ H) : (T.subgroupOf H).map H.subtype = T := by
  rw [subgroupOf_map_subtype, inf_of_le_left hTH]

theorem isSylowOf_map [Fact p.Prime] [Finite G] {H : Subgroup G} (T : Sylow p ↥H) :
    IsSylowOf p H ((T : Subgroup ↥H).map H.subtype) := by
  refine ⟨map_subtype_le _, T.isPGroup'.map _, ?_⟩
  have e : ((T : Subgroup ↥H).map H.subtype).relIndex H = (T : Subgroup ↥H).index := by
    rw [relIndex, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  rw [e]
  exact T.not_dvd_index

theorem exists_isSylowOf_le [Fact p.Prime] [Finite G] {H P : Subgroup G} (hP : IsPGroup p P)
    (hPH : P ≤ H) : ∃ T, IsSylowOf p H T ∧ P ≤ T := by
  obtain ⟨T, hT⟩ := (hP.comap_subtype (K := H)).exists_le_sylow
  refine ⟨_, isSylowOf_map T, fun x hx => ⟨⟨x, hPH hx⟩, hT hx, rfl⟩⟩

theorem IsSylowOf.map_conj {H T : Subgroup G} (h : IsSylowOf p H T) (g : G) :
    IsSylowOf p (H.map (MulAut.conj g).toMonoidHom) (T.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨map_mono h.1, h.2.1.map _, ?_⟩
  rw [relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact h.2.2

theorem IsSylowOf.exists_conj_le [Fact p.Prime] [Finite G] {R A B : Subgroup G}
    (hA : IsSylowOf p R A) (hBR : B ≤ R) (hBp : IsPGroup p B) :
    ∃ r ∈ R, ∀ y ∈ B, r⁻¹ * y * r ∈ A := by
  let SA : Sylow p R := hA.toSylow
  obtain ⟨X, hX⟩ := (hBp.comap_subtype (K := R)).exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R X SA
  refine ⟨((r⁻¹ : R) : G), (r⁻¹ : R).2, fun y hy => ?_⟩
  have hmem : MulAut.conj r • (⟨y, hBR hy⟩ : R) ∈ ((r • X : Sylow p R) : Subgroup R) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _
      (hX (show (⟨y, hBR hy⟩ : R) ∈ B.comap R.subtype from hy))
  rw [hr] at hmem
  have hA' : (MulAut.conj r • (⟨y, hBR hy⟩ : R) : R) ∈ A.subgroupOf R := by
    have := hmem
    rwa [IsSylowOf.coe_toSylow] at this
  rw [mem_subgroupOf] at hA'
  simpa [MulAut.smul_def, MulAut.conj_apply] using hA'

end Sylow

section Control

variable {G : Type} [Group G]

abbrev nK (T : Subgroup G) : Subgroup G :=
  Subgroup.normalizer ((kLowInfty T : Subgroup G) : Set G)

@[expose] def ControlsTransfer (p : ℕ) (X : Type) [Group X] : Prop :=
  ∀ S : Sylow p X, (S : Subgroup X) ⊓ commutator X ≤ ⁅nK (S : Subgroup X), nK (S : Subgroup X)⁆

theorem map_kLowInfty {H T : Subgroup G} (hTH : T ≤ H) :
    (kLowInfty (T.subgroupOf H)).map H.subtype = kLowInfty T := by
  rw [← CFSG.GH74.GLS.Stage2.Signalizer.L53.kLowInfty_map' H.subtype H.subtype_injective,
    map_subgroupOf_eq hTH]

theorem ControlsTransfer.sub {p : ℕ} [Fact p.Prime] {H T : Subgroup G}
    (hH : ControlsTransfer p ↥H) (hT : IsSylowOf p H T) :
    T ⊓ ⁅H, H⁆ ≤ ⁅H ⊓ nK T, H ⊓ nK T⁆ := by
  have hN : (nK (T.subgroupOf H)).map H.subtype ≤ H ⊓ nK T := by
    refine le_inf (map_subtype_le _) ?_
    have := le_normalizer_map (H := kLowInfty (T.subgroupOf H)) H.subtype
    rwa [map_kLowInfty hT.1] at this
  rintro x ⟨hxT, hxc⟩
  rw [← map_subtype_commutator] at hxc
  obtain ⟨x', hx', rfl⟩ := hxc
  have hx'T : x' ∈ (hT.toSylow : Subgroup ↥H) := by
    rw [IsSylowOf.coe_toSylow, mem_subgroupOf]
    exact hxT
  have h1 := hH hT.toSylow ⟨hx'T, hx'⟩
  rw [IsSylowOf.coe_toSylow] at h1
  have h2 : (x' : G) ∈ (⁅nK (T.subgroupOf H), nK (T.subgroupOf H)⁆).map H.subtype :=
    ⟨x', h1, rfl⟩
  rw [map_commutator] at h2
  exact commutator_mono hN hN h2

end Control

section Chief

variable {G : Type*} [Group G]

theorem comm_le_of_chief {P X Y : Subgroup G} (hP : Group.IsNilpotent ↥P) (hPn : P.Normal)
    (hXP : X ≤ P) (hc : IsChiefPair X Y) : ⁅X, P⁆ ≤ Y := by
  have hXn := hc.1
  have hYn := hc.2.1
  have hYX : Y < X := hc.2.2.1
  have hZn : (⁅X, P⁆ ⊔ Y).Normal := by infer_instance
  have hZX : ⁅X, P⁆ ⊔ Y ≤ X := sup_le (Subgroup.commutator_le_left X P) hYX.le
  have hPY : P ≤ normalizer (Y : Set G) := by
    intro t _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact (CFSG.GH74.GLS.Stage2.Signalizer.L53.nconj_iff hYn t).symm
  rcases hc.2.2.2 _ hZn le_sup_right hZX with h | h
  · rw [← h]; exact le_sup_left
  · exfalso
    exact hYX.not_ge (CFSG.GH74.GLS.Stage2.Signalizer.L53.le_of_le_comm_sup hP hXP hPY h.ge)

theorem comm_self_le_of_chief {P X Y : Subgroup G} (hP : Group.IsNilpotent ↥P) (hPn : P.Normal)
    (hXP : X ≤ P) (hc : IsChiefPair X Y) : ⁅X, X⁆ ≤ Y :=
  (commutator_mono le_rfl hXP).trans (comm_le_of_chief hP hPn hXP hc)

end Chief

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB

end
