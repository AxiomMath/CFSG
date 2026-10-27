module

public import CFSG.HardMathSupport.Timmesfeld.Balance.CompCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Balance.Faithful

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Balance

section Fix

variable {K : Type*} [Group K]

@[expose] def fixSub (g : MulAut K) : Subgroup K where
  carrier := {x | g x = x}
  mul_mem' := fun {a b} ha hb => by
    change g (a * b) = a * b
    rw [map_mul]
    change g a = a at ha
    change g b = b at hb
    rw [ha, hb]
  one_mem' := map_one g
  inv_mem' := fun {a} ha => by
    change g a⁻¹ = a⁻¹
    rw [map_inv]
    change g a = a at ha
    rw [ha]

theorem mem_fixSub {g : MulAut K} {x : K} : x ∈ fixSub g ↔ g x = x := Iff.rfl

theorem fixSub_eq_top_iff {g : MulAut K} : fixSub g = ⊤ ↔ g = 1 := by
  constructor
  · intro h
    ext x
    exact mem_fixSub.1 (h ▸ Subgroup.mem_top x)
  · rintro rfl
    exact eq_top_iff.2 fun x _ => rfl

theorem mul_conj_mul_inv (g : MulAut K) (x : K) :
    g * MulAut.conj x * g⁻¹ = MulAut.conj (g x) := by
  ext y
  simp [MulAut.conj_apply]

theorem mem_fixSub_of_commute (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {g : MulAut K} {x : K} (h : g * MulAut.conj x = MulAut.conj x * g) : x ∈ fixSub g := by
  apply hinj
  rw [← mul_conj_mul_inv, h, mul_assoc, mul_inv_cancel, mul_one]

end Fix

section Delta

variable {M : Type*} [Group M] {p : ℕ}

theorem localDeltaIn_antitone (H : Subgroup M) {D E : Subgroup M} (h : E ≤ D) :
    localDeltaIn p H D ≤ localDeltaIn p H E := by
  unfold localDeltaIn
  exact le_iInf₂ fun e he => le_iInf fun he1 => iInf₂_le_of_le e (h he) (iInf_le_of_le he1 le_rfl)

theorem le_core_of_mem_localDeltaIn {H D : Subgroup M} {g : M} (hg : g ∈ localDeltaIn p H D)
    {d : M} (hd : d ∈ D) (hd1 : d ≠ 1) :
    g ∈ GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set M)) := by
  unfold localDeltaIn at hg
  simp only [Subgroup.mem_iInf] at hg
  exact hg d hd hd1

theorem commute_of_mem_localDeltaIn {H D : Subgroup M} {g : M} (hg : g ∈ localDeltaIn p H D)
    {d : M} (hd : d ∈ D) : g * d = d * g := by
  by_cases hd1 : d = 1
  · rw [hd1, mul_one, one_mul]
  · have h1 := le_core_of_mem_localDeltaIn hg hd hd1
    have h2 : g ∈ H ⊓ Subgroup.centralizer ({d} : Set M) :=
      gLAPPrimeCoreOf_le_self' _ h1
    have h3 := (Subgroup.mem_inf.1 h2).2
    exact (Subgroup.mem_centralizer_singleton_iff.1 h3)

variable [Finite M]

theorem coprime_orderOf_of_mem_localDeltaIn (hp : p.Prime) {H D : Subgroup M} {g : M}
    (hg : g ∈ localDeltaIn p H D) {d : M} (hd : d ∈ D) (hd1 : d ≠ 1) :
    Nat.Coprime p (orderOf g) := by
  have h1 := le_core_of_mem_localDeltaIn hg hd hd1
  exact (coprime_card_gLAPPrimeCoreOf' hp _).coprime_dvd_right
    (Subgroup.orderOf_dvd_natCard _ h1)

end Delta

section Component

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

theorem le_fixSub_of_component (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {H E : Subgroup (MulAut K)} {g : MulAut K} (hg : g ∈ localDeltaIn p H E)
    {e : MulAut K} (he : e ∈ E) (he1 : e ≠ 1) {T : Subgroup K}
    (hTC : T.map (MulAut.conj : K →* MulAut K) ≤ H ⊓ Subgroup.centralizer ({e} : Set (MulAut K)))
    (hcomp : CFSG.IsComponent ((T.map (MulAut.conj : K →* MulAut K)).subgroupOf
      (H ⊓ Subgroup.centralizer ({e} : Set (MulAut K)))))
    (hTp : ¬ Nat.Coprime p (Nat.card T)) : T ≤ fixSub g := by
  intro x hx
  refine mem_fixSub_of_commute hinj ?_
  have hcard : Nat.card (T.map (MulAut.conj : K →* MulAut K)) = Nat.card T :=
    Subgroup.card_map_of_injective hinj
  exact commute_of_mem_gLAPPrimeCoreOf_of_isComponent hp hTC hcomp (by rwa [hcard])
    (le_core_of_mem_localDeltaIn hg he he1) _ (Subgroup.mem_map_of_mem _ hx)

end Component

end CFSG.HardMathSupport.Timmesfeld.CrossChar
