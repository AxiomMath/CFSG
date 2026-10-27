module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Index
public import CFSG.LieType.SeitzGeneration.ExcTorusSylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders

section Abstract

variable {p : ℕ}

theorem card_pow_eq_one_of_surjective {B T : Type*} [CommGroup B] [Finite B] [Group T]
    (hp : p.Prime) (φ : B →* T) (hφ : Function.Surjective φ) (hker : ¬ p ∣ Nat.card φ.ker) :
    Nat.card {x : T // x ^ p = 1} = Nat.card {b : B // b ^ p = 1} := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun b => ⟨φ b.1, by rw [← map_pow, b.2, map_one]⟩) ⟨?_, ?_⟩)
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    have h0 : φ a = φ b := congrArg Subtype.val h
    have h1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, h0, mul_inv_cancel]
    have h2 : (a * b⁻¹) ^ p = 1 := by rw [mul_pow, inv_pow, ha, hb, inv_one, mul_one]
    have h3 : orderOf (a * b⁻¹) ∣ Nat.card φ.ker := by
      have := orderOf_dvd_natCard (⟨a * b⁻¹, h1⟩ : φ.ker)
      rw [← Subgroup.orderOf_coe] at this
      exact this
    have h4 : orderOf (a * b⁻¹) ∣ p := orderOf_dvd_of_pow_eq_one h2
    rcases (Nat.dvd_prime hp).1 h4 with h5 | h5
    · rw [orderOf_eq_one_iff, mul_inv_eq_one] at h5
      exact Subtype.ext h5
    · exact absurd (h5 ▸ h3) hker
  · rintro ⟨x, hx⟩
    obtain ⟨t, rfl⟩ := hφ x
    set c := Nat.card φ.ker with hc
    have hcop : Nat.Coprime c p :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hker)
    obtain ⟨c', -, hc'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have htp : t ^ p ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hx]
    have htc : (t ^ p) ^ c = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (G := φ.ker) (x := ⟨t ^ p, htp⟩))
    refine ⟨⟨t ^ (c * c'), ?_⟩, ?_⟩
    · rw [← pow_mul, show c * c' * p = p * c * c' by ring, pow_mul, pow_mul, htc, one_pow]
    · apply Subtype.ext
      change φ (t ^ (c * c')) = φ t
      rw [map_pow, ← Nat.div_add_mod (c * c') p, hc', pow_add, pow_mul, hx, one_pow, one_mul,
        pow_one]

theorem card_pi_pow_eq_one {M : Type*} [Group M] (r : ℕ) :
    Nat.card {t : Fin r → M // t ^ p = 1} = Nat.card {a : M // a ^ p = 1} ^ r := by
  have e : {t : Fin r → M // t ^ p = 1} ≃ (Fin r → {a : M // a ^ p = 1}) :=
    (Equiv.subtypeEquivRight fun t => by
      rw [funext_iff]
      simp only [Pi.pow_apply, Pi.one_apply]).trans Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin]

theorem card_units_pow_eq_one {K : Type*} [Field K] [Finite K] (hdvd : p ∣ Nat.card K - 1) :
    Nat.card {a : Kˣ // a ^ p = 1} = p := by
  have h := IsCyclic.card_powMonoidHom_ker (G := Kˣ) p
  rw [Nat.card_units, Nat.gcd_eq_right hdvd] at h
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)).trans h
  rw [MonoidHom.mem_ker]
  rfl

end Abstract

section Torus


variable {τ : Tag} {K : Type} [Field K]

theorem torusSub_le_monomialSub : torusSub τ K ≤ monomialSub τ K := by
  rw [← borelSub_inf_monomialSub]
  exact inf_le_right

theorem conj_mem_torusSub {n h : adjointGroup τ K} (hn : n ∈ monomialSub τ K)
    (hh : h ∈ torusSub τ K) : n * h * n⁻¹ ∈ torusSub τ K := by
  have hhN : h ∈ monomialSub τ K := torusSub_le_monomialSub hh
  set m : monomialSub τ K := ⟨n * h * n⁻¹,
    (monomialSub τ K).mul_mem ((monomialSub τ K).mul_mem hn hhN) ((monomialSub τ K).inv_mem hn)⟩
  have hm : m = ⟨n, hn⟩ * ⟨h, hhN⟩ * (⟨n, hn⟩ : monomialSub τ K)⁻¹ := rfl
  have h1 : monomialSubHom (⟨h, hhN⟩ : monomialSub τ K) = 1 := (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.monomialSubHom_ker_iff _).2 hh
  have h2 : monomialSubHom m = 1 := by
    rw [hm, map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  exact (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.monomialSubHom_ker_iff m).1 h2

variable [Finite K]

theorem exists_torsion_torusSub {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card K - 1)
    (hker : ¬ p ∣ Nat.card (zpowMatrix (G := Kˣ) τ.cartan).ker) :
    ∃ A : Subgroup (adjointGroup τ K), A ≤ monomialSub τ K ∧
      monomialSub τ K ≤ normalizer (A : Set (adjointGroup τ K)) ∧ IsElemAbelian p A ∧
      Nat.card A = p ^ τ.rank := by
  have hT : IsMulCommutative (torusSub τ K) :=
    ⟨⟨fun a b => Subtype.ext (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.torusSub_comm _ a.2 _
      b.2)⟩⟩
  set A := CFSG.LieType.SeitzGeneration.torsionSubgroup (torusSub τ K) hT p with hA
  have hmemA : ∀ x, x ∈ A ↔ x ∈ torusSub τ K ∧ x ^ p = 1 := fun x => Iff.rfl
  refine ⟨A, fun x hx => torusSub_le_monomialSub ((hmemA x).1 hx).1, ?_, ?_, ?_⟩
  · intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe, hmemA]
    constructor
    · rintro ⟨hh, hhp⟩
      exact ⟨conj_mem_torusSub hn hh, by rw [conj_pow, hhp, mul_one, mul_inv_cancel]⟩
    · rintro ⟨hh, hhp⟩
      have e : h = n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ := by group
      refine ⟨e ▸ conj_mem_torusSub ((monomialSub τ K).inv_mem hn) hh, ?_⟩
      rw [e, conj_pow, hhp, mul_one, mul_inv_cancel]
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ((hmemA x).1 hx).2⟩
    exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.torusSub_comm _ ((hmemA _).1 a.2).1 _
      ((hmemA _).1 b.2).1
  ·
    have hle : torusGroup τ K ≤ adjointGroup τ K :=
      torusGroup_le_borelGroup.trans borelGroup_le_adjointGroup'
    set e := Subgroup.subgroupOfEquivOfLe hle with he
    set φ : (Fin τ.rank → Kˣ) →* torusSub τ K := e.symm.toMonoidHom.comp (torusCoordHom τ K)
      with hφ
    have hφs : Function.Surjective φ := e.symm.surjective.comp torusCoordHom_surjective
    have hφk : φ.ker = (zpowMatrix (G := Kˣ) τ.cartan).ker := by
      ext t
      simp only [MonoidHom.mem_ker, hφ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        Function.comp_apply, MulEquiv.map_eq_one_iff]
      exact torusCoordHom_eq_one_iff t
    have h1 := card_pow_eq_one_of_surjective hp φ hφs (by rw [hφk]; exact hker)
    rw [card_pi_pow_eq_one, card_units_pow_eq_one hdvd] at h1
    rw [← h1]
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, ((hmemA _).1 x.2).1⟩, Subtype.ext ((hmemA _).1 x.2).2⟩
        invFun := fun y => ⟨y.1.1, (hmemA _).2 ⟨y.1.2, congrArg Subtype.val y.2⟩⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }

end Torus

end CFSG.LocalAnalysis.RankFourTheoremC
