module

public import CFSG.Sporadic.SmallOddCore.Assembly
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.NoSigArith
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.PlaneKill
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.RankOK

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.SmallOddCore

theorem conj_injective_of_center_bot_sg {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : x ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun y => by
    have h1 := congrArg (fun f : MulAut X => f y) hx
    change x * y * x⁻¹ = y at h1
    calc y * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  rw [hZ] at hc
  exact Subgroup.mem_bot.1 hc

section Model

variable {M : Type*} [Group M] {P R : Subgroup M} (h : AutModel P R)

theorem autModel_hom_conj (a : ↥P) : h.hom (MulAut.conj a) = (a : M) :=
  h.elt_eq (h.le a.2) fun p => by simp [MulAut.conj_apply]

include h in
theorem autModel_center_eq_bot : Subgroup.center ↥P = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have h1 : (z : M) = 1 := by
    refine h.inj (z : M) (h.le z.2) fun p hp => ?_
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨p, hp⟩).symm
  exact Subtype.ext h1

end Model

@[expose] def PFree (p : ℕ) {M : Type*} [Group M] (S : Subgroup M) : Prop :=
  ∀ u ∈ S, Nat.Coprime (orderOf u) p → u = 1

theorem PFree.of_isPGroup {M : Type*} [Group M] {p : ℕ} {S : Subgroup M} (h : IsPGroup p S) :
    PFree p S := by
  intro u hu hcop
  obtain ⟨n, hn⟩ := h ⟨u, hu⟩
  have hn' : u ^ (p ^ n) = 1 := congrArg Subtype.val hn
  have hcop' : Nat.Coprime (orderOf u) (p ^ n) := Nat.Coprime.pow_right n hcop
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop' (orderOf_dvd_of_pow_eq_one hn'))

theorem isElemAbelian_of_map_injective' {X Y : Type*} [Group X] [Group Y] {f : X →* Y}
    (hf : Function.Injective f) {p : ℕ} {P : Subgroup X} (hP : IsElemAbelian p (P.map f)) :
    IsElemAbelian p P := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val
      (hP.1.is_comm.comm ⟨f a, a, a.2, rfl⟩ ⟨f b, b, b.2, rfl⟩)
  · rw [map_pow, map_one]
    exact hP.2 _ ⟨x, hx, rfl⟩

theorem noSig_of_autModel_rank {M : Type*} [Group M] [Finite M] {P R : Subgroup M}
    (h : AutModel P R) {p : ℕ} (hp : p.Prime) (Q0 : Subgroup ↥P)
    (hQ : IsElemAbelian p Q0) (hQ2 : Nat.card Q0 = p ^ 2)
    (hA : PFree p (R ⊓ Subgroup.centralizer ((Q0.map P.subtype : Subgroup M) : Set M) :
      Subgroup M))
    (hB : ∀ y : ↥P, y ∈ Q0 → y ≠ 1 →
      RankOK p (R ⊓ Subgroup.centralizer ({(y : M)} : Set M) : Subgroup M)) :
    NoSig p (Q0.map (MulAut.conj : ↥P →* MulAut ↥P)) := by
  haveI : Finite ↥P := inferInstance
  have hcen : Subgroup.center ↥P = ⊥ := autModel_center_eq_bot h
  have hinj : Function.Injective (MulAut.conj : ↥P →* MulAut ↥P) :=
    conj_injective_of_center_bot_sg hcen
  have hEel : IsElemAbelian p (Q0.map (MulAut.conj : ↥P →* MulAut ↥P)) := hQ.map _
  have hEcard : Nat.card (Q0.map (MulAut.conj : ↥P →* MulAut ↥P)) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj, hQ2]
  haveI : Finite (MulAut ↥P) :=
    Finite.of_injective (fun σ : MulAut ↥P => (σ : ↥P → ↥P)) DFunLike.coe_injective
  intro T hTcop hET
  refine noSig_of_rank hp hEel hEcard ?_ ?_ T hTcop hET
  ·
    intro u hu hcomm
    set x : M := h.hom u with hx
    have hxR : x ∈ R := h.elt_mem u
    have hxC : x ∈ Subgroup.centralizer ((Q0.map P.subtype : Subgroup M) : Set M) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      have hmem : (MulAut.conj a : MulAut ↥P) ∈ Q0.map (MulAut.conj : ↥P →* MulAut ↥P) :=
        ⟨a, ha, rfl⟩
      have := congrArg h.hom (hcomm _ hmem)
      rw [map_mul, map_mul, autModel_hom_conj h] at this
      exact this.symm
    have hord : orderOf x = orderOf u := orderOf_injective h.hom h.hom_injective u
    have hx2 : x = 1 := hA x ⟨hxR, hxC⟩ (by rw [hord]; exact hu)
    apply h.hom_injective
    rw [map_one]
    exact hx2
  ·
    intro e he he1 q hq hqp V hV hVel hVne
    obtain ⟨a, ha, rfl⟩ := he
    have ha1 : a ≠ 1 := by
      intro h1
      apply he1
      rw [h1, map_one]
    have hmap : V.map h.hom ≤ R ⊓ Subgroup.centralizer ({(a : M)} : Set M) := by
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨h.elt_mem v, ?_⟩
      have hv' : v ∈ Subgroup.centralizer ({(MulAut.conj a : MulAut ↥P)} : Set (MulAut ↥P)) := hV hv
      show h.hom v ∈ Subgroup.centralizer ({(a : M)} : Set M)
      rw [Subgroup.mem_centralizer_singleton_iff] at hv' ⊢
      have := congrArg h.hom hv'
      rw [map_mul, map_mul, autModel_hom_conj h] at this
      exact this
    have hne : V.map h.hom ≠ ⊥ := fun hbot => hVne
      ((Subgroup.map_eq_bot_iff_of_injective V h.hom_injective).1 hbot)
    have hcard : Nat.card (V.map h.hom) = Nat.card V :=
      Subgroup.card_map_of_injective h.hom_injective
    have := hB a ha ha1 q hq hqp (V.map h.hom) hmap (hVel.map _) hne
    rwa [hcard] at this

end CFSG.HardMathSupport.Dickson.I271
