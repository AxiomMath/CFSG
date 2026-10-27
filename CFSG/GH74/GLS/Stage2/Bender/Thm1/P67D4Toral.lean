module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OddIdx
public import CFSG.GH74.GLS.Stage2.OddAut.LangR
public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem exists_unit_pow_sub_one_eq {K : Type} [Field K] [Finite K] {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (u : Kˣ) (hu : u ^ (q ^ 2 + q + 1) = 1) :
    ∃ b : Kˣ, b ^ (q - 1) = u := by
  classical
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = q ^ 3 - 1 := by rw [Nat.card_units, hK]
  have hord : orderOf γ = q ^ 3 - 1 := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hγ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hγ u)
  have h1 : γ ^ (k * ((q ^ 2 + q + 1 : ℕ) : ℤ)) = 1 := by
    rw [zpow_mul, hk, zpow_natCast, hu]
  have h2 := (orderOf_dvd_iff_zpow_eq_one.2 h1)
  rw [hord] at h2
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have hm : (m + 1) ^ 3 - 1 = m * ((m + 1) ^ 2 + (m + 1) + 1) := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [hm] at h2
  have hN0 : (((m + 1) ^ 2 + (m + 1) + 1 : ℕ) : ℤ) ≠ 0 := by positivity
  have h3 : ((m : ℕ) : ℤ) ∣ k := by
    have : ((m : ℕ) : ℤ) * (((m + 1) ^ 2 + (m + 1) + 1 : ℕ) : ℤ) ∣
        k * (((m + 1) ^ 2 + (m + 1) + 1 : ℕ) : ℤ) := by exact_mod_cast h2
    exact (mul_dvd_mul_iff_right hN0).1 this
  obtain ⟨j, hj⟩ := h3
  refine ⟨γ ^ j, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, show (m + 1 - 1 : ℕ) = m by omega, mul_comm, ← hj, hk]
  
theorem normSeq_three {S : Type*} [Group S] (Φ : MulAut S) (g : S) :
    CFSG.GH74.GLS.Stage2.OddAut.normSeq Φ g 3 = g * Φ g * Φ (Φ g) := by
  simp [CFSG.GH74.GLS.Stage2.OddAut.normSeq, pow_succ, MulAut.mul_apply]

open CFSG.Blueprint.Chevalley in
theorem d4_perm_zero : TwistTag.D4.perm (0 : Fin 4) = (1 : Fin 4) := rfl

open CFSG.Blueprint.Chevalley in
theorem d4_perm_one : TwistTag.D4.perm (1 : Fin 4) = (3 : Fin 4) := rfl

open CFSG.Blueprint.Chevalley in
theorem d4_perm_two : TwistTag.D4.perm (2 : Fin 4) = (2 : Fin 4) := rfl

open CFSG.Blueprint.Chevalley in
theorem d4_perm_three : TwistTag.D4.perm (3 : Fin 4) = (0 : Fin 4) := rfl

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem d4_toral_reduction {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hn : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hN : normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = 1) :
    ∃ t s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      fieldActor (t := TwistTag.D4) σ σ s = s ∧ s ^ 3 = 1 ∧
      t * n * (fieldActor (t := TwistTag.D4) σ σ t)⁻¹ = s ∧
      ∃ d : Kˣ, Units.map σ.toRingHom.toMonoidHom d = d ∧ d ^ 3 = 1 ∧
        (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] := by
  classical
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hpar : ringChar K = 2 ∨ ∃ m, Odd m ∧ ∀ c, σ c = c ^ m := Or.inr ⟨p ^ f, hodd, hσ⟩
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_inf.1 hn).1
  have hΓ : (n : ModGL TwistTag.D4.tag K) ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedRootGroup_le _ _ _ n.2
  have hcompat : ∀ i, l (TwistTag.D4.perm i) = Units.map σ.toRingHom.toMonoidHom (l i) := by
    apply compat_of_twistHom_rootDiagUnit
    rw [← hl]
    exact ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hΓ).2
  set σU : Kˣ →* Kˣ := Units.map σ.toRingHom.toMonoidHom with hσU
  have hσUpow : ∀ x : Kˣ, σU x = x ^ (p ^ f) := fun x => Units.ext (by simp [σU, hσ])
  have hσU3 : ∀ x : Kˣ, σU (σU (σU x)) = x := fun x => Units.ext (hσ3 x)
  have hN' : rootDiagUnit TwistTag.D4.tag
      (l * (fun i => σU (l i)) * (fun i => σU (σU (l i)))) = 1 := by
    have h := congrArg Subtype.val hN
    rw [normSeq_three] at h
    change (n : ModGL TwistTag.D4.tag K) *
      Units.map (entrywiseHom σ.toRingHom) (n : ModGL TwistTag.D4.tag K) *
      Units.map (entrywiseHom σ.toRingHom)
        (Units.map (entrywiseHom σ.toRingHom) (n : ModGL TwistTag.D4.tag K)) = 1 at h
    rw [hl, units_map_entrywiseHom_rootDiagUnit, units_map_entrywiseHom_rootDiagUnit,
      ← rootDiagUnit_mul, ← rootDiagUnit_mul] at h
    exact h
  have hcocycle : ∀ i, l i * σU (l i) * σU (σU (l i)) = 1 := fun i => by
    have := congrFun (rootDiagUnit_injective (hN'.trans rootDiagUnit_one.symm)) i
    simpa using this
  have hq2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  set q := p ^ f with hqdef
  have hl0N : l (0 : Fin 4) ^ (q ^ 2 + q + 1) = 1 := by
    have h0 := hcocycle (0 : Fin 4)
    rw [hσUpow, hσUpow] at h0
    have e : l (0 : Fin 4) * l (0 : Fin 4) ^ q * (l (0 : Fin 4) ^ q) ^ q =
        l (0 : Fin 4) ^ (q ^ 2 + q + 1) := by
      rw [← pow_mul, sq, pow_add, pow_add, pow_one]
      ac_rfl
    rw [← e]
    exact h0
  obtain ⟨b, hb⟩ := exists_unit_pow_sub_one_eq hq2 hK (l (0 : Fin 4)) hl0N
  have hσb : σU b = b * l (0 : Fin 4) := by
    rw [hσUpow, ← hb, mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q)]
  have hl1 : l (1 : Fin 4) = σU (l (0 : Fin 4)) := by
    have := hcompat (0 : Fin 4)
    rwa [d4_perm_zero] at this
  have hl3 : l (3 : Fin 4) = σU (l (1 : Fin 4)) := by
    have := hcompat (1 : Fin 4)
    rwa [d4_perm_one] at this
  have hl2 : l (2 : Fin 4) = σU (l (2 : Fin 4)) := by
    have := hcompat (2 : Fin 4)
    rwa [d4_perm_two] at this
  have hσσb : σU (σU b) = σU b * l (1 : Fin 4) := by
    rw [hl1, ← map_mul, ← hσb]
  have hb3 : σU (σU b) * l (3 : Fin 4) = b := by
    have := hσU3 b
    rw [hσσb, map_mul, ← hl3] at this
    exact this
  have hσl2 : σU (l (2 : Fin 4)) = l (2 : Fin 4) := hl2.symm
  have hl2cube : l (2 : Fin 4) ^ 3 = 1 := by
    have := hcocycle (2 : Fin 4)
    rw [hσl2, hσl2] at this
    rw [pow_three]
    simpa [mul_assoc] using this
  let u : Fin TwistTag.D4.tag.rank → Kˣ := ![b, σU b, 1, σU (σU b)]
  let sv : Fin TwistTag.D4.tag.rank → Kˣ := ![1, 1, l (2 : Fin 4), 1]
  have hucompat : ∀ i, u (TwistTag.D4.perm i) = σU (u i) := by
    intro i
    fin_cases i
    · exact rfl
    · exact rfl
    · show u (TwistTag.D4.perm (2 : Fin 4)) = σU (u (2 : Fin 4))
      rw [d4_perm_two]
      exact (map_one σU).symm
    · show u (TwistTag.D4.perm (3 : Fin 4)) = σU (u (3 : Fin 4))
      rw [d4_perm_three]
      exact (hσU3 b).symm
  have hsvcompat : ∀ i, sv (TwistTag.D4.perm i) = σU (sv i) := by
    intro i
    fin_cases i
    · show sv (TwistTag.D4.perm (0 : Fin 4)) = σU (sv (0 : Fin 4))
      rw [d4_perm_zero]
      exact (map_one σU).symm
    · show sv (TwistTag.D4.perm (1 : Fin 4)) = σU (sv (1 : Fin 4))
      rw [d4_perm_one]
      exact (map_one σU).symm
    · show sv (TwistTag.D4.perm (2 : Fin 4)) = σU (sv (2 : Fin 4))
      rw [d4_perm_two]
      exact hl2
    · show sv (TwistTag.D4.perm (3 : Fin 4)) = σU (sv (3 : Fin 4))
      rw [d4_perm_three]
      exact (map_one σU).symm
  have hmemt := rootDiagUnit_mem_graphFixedRootGroup_triality σ hσ3 hpar hucompat
  have hmems := rootDiagUnit_mem_graphFixedRootGroup_triality σ hσ3 hpar hsvcompat
  have hfun : u * l * (fun i => (σU (u i))⁻¹) = sv := by
    funext i
    fin_cases i
    · show b * l (0 : Fin 4) * (σU b)⁻¹ = 1
      rw [hσb]
      exact mul_inv_cancel _
    · show σU b * l (1 : Fin 4) * (σU (σU b))⁻¹ = 1
      rw [hσσb]
      exact mul_inv_cancel _
    · show (1 : Kˣ) * l (2 : Fin 4) * (σU 1)⁻¹ = l (2 : Fin 4)
      simp
    · show σU (σU b) * l (3 : Fin 4) * (σU (σU (σU b)))⁻¹ = 1
      rw [hσU3 b, hb3]
      exact mul_inv_cancel _
  have hsvfix : ∀ i, σU (sv i) = sv i := by
    intro i
    fin_cases i
    · exact map_one σU
    · exact map_one σU
    · exact hσl2
    · exact map_one σU
  refine ⟨⟨_, hmemt⟩, ⟨_, hmems⟩, ?_, ?_, ?_, l (2 : Fin 4), hσl2, hl2cube, rfl⟩
  · apply Subtype.ext
    show Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit TwistTag.D4.tag sv) =
      rootDiagUnit TwistTag.D4.tag sv
    rw [units_map_entrywiseHom_rootDiagUnit]
    exact congrArg _ (funext hsvfix)
  · apply Subtype.ext
    show (rootDiagUnit TwistTag.D4.tag sv) ^ 3 = 1
    rw [rootDiagUnit_pow, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)]
    refine congrArg _ (funext fun i => ?_)
    fin_cases i
    · exact one_pow 3
    · exact one_pow 3
    · exact hl2cube
    · exact one_pow 3
  · apply Subtype.ext
    show rootDiagUnit TwistTag.D4.tag u * (n : ModGL TwistTag.D4.tag K) *
      (Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit TwistTag.D4.tag u))⁻¹ =
        rootDiagUnit TwistTag.D4.tag sv
    rw [hl, units_map_entrywiseHom_rootDiagUnit, rootDiagUnit_inv, ← rootDiagUnit_mul,
      ← rootDiagUnit_mul]
    exact congrArg _ hfun

theorem d4_toral_conj {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hn : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hN : normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = 1) :
    ∃ y s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      fieldActor (t := TwistTag.D4) σ σ s = s ∧ s ^ 3 = 1 ∧
      MulAut.conj y * (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) * (MulAut.conj y)⁻¹ =
        MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ ∧
      ∃ d : Kˣ, Units.map σ.toRingHom.toMonoidHom d = d ∧ d ^ 3 = 1 ∧
        (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] := by
  obtain ⟨t, s, hs, hs3, hts, hd⟩ := d4_toral_reduction hp hp2 hf K hK σ hσ n hn hN
  refine ⟨t, s, hs, hs3, ?_, hd⟩
  rw [← hts]
  exact conj_twist_eq _ _ _

end CFSG.GH74.GLS.Stage2.Bender.Thm1
