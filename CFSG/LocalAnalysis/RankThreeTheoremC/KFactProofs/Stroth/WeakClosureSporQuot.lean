module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLines

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem isMulCommutative_sylow_of [Fact p.Prime] (S T : Sylow p K)
    (h : IsMulCommutative (S : Subgroup K)) : IsMulCommutative (T : Subgroup K) := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K S T
  have hT : (T : Subgroup K) = (S : Subgroup K).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul]
    rfl
  have key : ∀ z : K, z ∈ (T : Subgroup K) →
      ∃ x ∈ (S : Subgroup K), (MulAut.conj c).toMonoidHom x = z := by
    intro z hz
    rw [hT] at hz
    exact Subgroup.mem_map.1 hz
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  obtain ⟨x, hx, hxa⟩ := key a a.2
  obtain ⟨y, hy, hyb⟩ := key b b.2
  have hxy := congrArg Subtype.val (h.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  simp only [Subgroup.coe_mul] at hxy ⊢
  rw [← hxa, ← hyb, ← map_mul, ← map_mul, hxy]

theorem not_isMulCommutative_sylow_of_small_centralizer [Fact p.Prime] {y : K} (hy : y ^ p = 1)
    {f m : ℕ} (hf : (Nat.card K).factorization p = f)
    (hC : Nat.card (Subgroup.centralizer ({y} : Set K)) ∣ m) (hm : ¬ p ^ f ∣ m)
    (S : Sylow p K) : ¬ IsMulCommutative (S : Subgroup K) := by
  intro hS
  have hyp : IsPGroup p (Subgroup.zpowers y) := by
    intro z
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 z.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  obtain ⟨S₀, hS₀⟩ := hyp.exists_le_sylow
  have hcomm := isMulCommutative_sylow_of S S₀ hS
  have hyS : y ∈ (S₀ : Subgroup K) := hS₀ (Subgroup.mem_zpowers y)
  have hle : (S₀ : Subgroup K) ≤ Subgroup.centralizer ({y} : Set K) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨z, hyS⟩)).symm
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [S₀.card_eq_multiplicity, hf] at hdvd
  exact hm (hdvd.trans hC)

theorem wcOn_of_surj_sylow [Fact p.Prime] {A : Type} [Group A] (M : Subgroup K) (f : M →* A)
    (hf : Function.Surjective f) (hA : ∀ S : Sylow p A, ¬ IsMulCommutative (S : Subgroup A)) :
    WCOn p K := by
  obtain ⟨R⟩ : Nonempty (Sylow p M) := inferInstance
  obtain ⟨S, hS⟩ := (R.isPGroup'.map M.subtype).exists_le_sylow
  refine WCOn.of_sylow S fun hc => ?_
  exfalso
  have hcommR : ∀ a ∈ (R : Subgroup M), ∀ b ∈ (R : Subgroup M), a * b = b * a := by
    intro a ha b hb
    have h1 : M.subtype a ∈ (S : Subgroup K) := hS ⟨a, ha, rfl⟩
    have h2 : M.subtype b ∈ (S : Subgroup K) := hS ⟨b, hb, rfl⟩
    have h3 := congrArg Subtype.val (hc.is_comm.comm ⟨M.subtype a, h1⟩ ⟨M.subtype b, h2⟩)
    apply Subtype.ext
    simpa using h3
  refine hA (R.mapSurjective hf) ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  have hx : (x : A) ∈ (R : Subgroup M).map f := x.2
  have hy : (y : A) ∈ (R : Subgroup M).map f := y.2
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hx
  obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 hy
  simp only [Subgroup.coe_mul]
  rw [← hax, ← hby, ← map_mul, ← map_mul, hcommR a ha b hb]

theorem alt9_sylow_three_not_comm (S : Sylow 3 (alternatingGroup (Fin 9))) :
    ¬ IsMulCommutative (S : Subgroup (alternatingGroup (Fin 9))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3c : (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 0 2).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  let y : alternatingGroup (Fin 9) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.Perm.mem_alternatingGroup.2 h3c.sign⟩
  have hy : y ^ 3 = 1 := Subtype.ext (by
    simp only [y, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← h3c.orderOf]
    exact pow_orderOf_eq_one _)
  have hN : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hf : (Nat.card (alternatingGroup (Fin 9))).factorization 3 = 4 := by
    rw [hN]
    exact factorization_eq_of_dvd Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
  have hC : Nat.card (Subgroup.centralizer ({y} : Set (alternatingGroup (Fin 9)))) ∣ 2160 := by
    rw [card_centralizer_subgroup (alternatingGroup (Fin 9)) y]
    have h1 := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.centralizer
      ({(y : Equiv.Perm (Fin 9))} : Set (Equiv.Perm (Fin 9))) ⊓ alternatingGroup (Fin 9) ≤ _)
    have h2 := Equiv.Perm.nat_card_centralizer (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 0 2)
    rw [h3c.cycleType] at h2
    have h4 : Nat.card (Subgroup.centralizer ({(y : Equiv.Perm (Fin 9))} :
        Set (Equiv.Perm (Fin 9)))) = 2160 := by
      rw [show (y : Equiv.Perm (Fin 9)) = Equiv.swap 0 1 * Equiv.swap 0 2 from rfl, h2]
      simp [Nat.factorial]
    rw [h4] at h1
    exact h1
  exact not_isMulCommutative_sylow_of_small_centralizer hy hf hC (by norm_num) S

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
