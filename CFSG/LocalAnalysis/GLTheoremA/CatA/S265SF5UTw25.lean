module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UCenter
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UCover
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UFix
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormP)
open CFSG.ClassicalGroups.UnitaryFlag (gramSU unitarySU mem_unitarySU_iff unitarySU_eq_gramSU
  commute_scalar)
open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (expHom expHom_apply diagHom_expHom_mem_unitarySU permGL_unitary
  det_permGL permGL_mul_diagHom_mul_inv)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective)
open CFSG.StandardType.TableBU (permGL_swap_not_mem_center)

section Model

variable {m : ℕ} {F : Type} [Field F]

private theorem exists_orderOf_pow_five (hF : UnitaryFieldData 2 m F) (h25 : 25 ∣ 2 ^ m + 1) :
    ∃ ε : Fˣ, orderOf (ε ^ 5) = 5 := by
  haveI := hF.finite
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hd : 25 ∣ orderOf g := by
    rw [hord, Nat.card_units, hF.card_eq_sq, show (1 : ℕ) = 1 ^ 2 from rfl, Nat.sq_sub_sq]
    exact Dvd.dvd.mul_right h25 _
  obtain ⟨k, hk⟩ := hd
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h0 => (orderOf_pos g).ne' (by rw [hk, h0, mul_zero])
  refine ⟨g ^ k, ?_⟩
  rw [← pow_mul, orderOf_pow_of_dvd (x := g) (n := k * 5) (by omega) ⟨5, by rw [hk]; ring⟩, hk,
    show 25 * k = 5 * (k * 5) by ring, Nat.mul_div_cancel 5 (n := k * 5) (by omega)]

private theorem exists_torus_of_dvd (hF : UnitaryFieldData 2 m F) (h25 : 25 ∣ 2 ^ m + 1) :
    ∃ (φ : Multiplicative (Fin 3 → ZMod 25) →*
        gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))
      (w : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)),
      w ^ 2 = 1 ∧ (∀ c : Fˣ, (w : GL (Fin 5) F) ≠ GeneralLinearGroup.scalar (Fin 5) c) ∧
      (∀ a, w * φ a = φ a * w) ∧
      (∀ a, ∃ c : Fˣ, ((φ a ^ 5 : gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) :
        GL (Fin 5) F) = GeneralLinearGroup.scalar (Fin 5) c) ∧
      ∃ av : (Fin 3 → Fin 5) → Multiplicative (Fin 3 → ZMod 25), ∀ v v' (c : Fˣ),
        ((φ (av v) * (φ (av v'))⁻¹ : gramSU hF ((1 : GL (Fin 5) F) :
          Matrix (Fin 5) (Fin 5) F)) : GL (Fin 5) F) = GeneralLinearGroup.scalar (Fin 5) c →
        v = v' := by
  haveI : CharP F 2 := hF.charP
  obtain ⟨ε, hζo⟩ := exists_orderOf_pow_five hF h25
  obtain ⟨ζ, hεζ⟩ : ∃ ζ, ε ^ 5 = ζ := ⟨_, rfl⟩
  rw [hεζ] at hζo
  have hζ5 : ζ ^ 5 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hζo
    norm_num at hζo
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → Fin 5 → Fˣ,
      ∀ j i, c j i = ε⁻¹ * if i = j.succ.succ then ζ else 1 := ⟨_, fun _ _ => rfl⟩
  have hc0 : ∀ j, c j 0 = ε⁻¹ := fun j => by
    rw [hc, if_neg (show (0 : Fin 5) ≠ j.succ.succ by revert j; decide), mul_one]
  have hc1 : ∀ j, c j 1 = ε⁻¹ := fun j => by
    rw [hc, if_neg (show (1 : Fin 5) ≠ j.succ.succ by revert j; decide), mul_one]
  have hc5 : ∀ j i, c j i ^ 5 = ε⁻¹ ^ 5 := fun j i => by
    rw [hc, mul_pow]
    split_ifs
    · rw [hζ5, mul_one]
    · rw [one_pow, mul_one]
  have hcp : ∀ j i, c j i ^ 25 = 1 := fun j i => by
    rw [show 25 = 5 * 5 from rfl, pow_mul, hc5, inv_pow, hεζ, inv_pow, hζ5, inv_one]
  have hcprod : ∀ j, ∏ i, c j i = 1 := fun j => by
    simp only [hc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [inv_pow, hεζ, inv_mul_cancel]
  obtain ⟨k, hk⟩ := h25
  have hcnorm : ∀ j i, c j i ^ (2 ^ m + 1) = 1 := fun j i => by rw [hk, pow_mul, hcp, one_pow]
  have hratio : ∀ a (j : Fin 3), expHom c hcp a j.succ.succ =
      expHom c hcp a 0 * ζ ^ (Multiplicative.toAdd a j).val := fun a j => by
    have h0 : expHom c hcp a 0 = ∏ l, ε⁻¹ ^ (Multiplicative.toAdd a l).val := by
      rw [expHom_apply]
      exact Finset.prod_congr rfl fun l _ => by rw [hc0]
    rw [h0, expHom_apply]
    simp only [hc, mul_pow, Finset.prod_mul_distrib, Fin.succ_inj, ite_pow, one_pow,
      Finset.prod_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hdiag : ∀ s : Fˣ, diagHom 5 (fun _ => s) = GeneralLinearGroup.scalar (Fin 5) s :=
    fun s => Units.ext (by rw [coe_diagHom, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply])
  have hHS : unitarySU 2 m F 5 = gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) :=
    unitarySU_eq_gramSU hF 5
  have hmem : ∀ a, diagHom 5 (expHom c hcp a) ∈
      gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := fun a => by
    rw [← hHS]
    exact diagHom_expHom_mem_unitarySU hF c hcp hcprod hcnorm a
  obtain ⟨φ, hφ⟩ : ∃ φ : Multiplicative (Fin 3 → ZMod 25) →*
      gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F),
      ∀ a, (φ a : GL (Fin 5) F) = diagHom 5 (expHom c hcp a) :=
    ⟨((diagHom 5).comp (expHom c hcp)).codRestrict _ hmem, fun _ => rfl⟩
  have hi01 : (0 : Fin 5) ≠ 1 := by decide
  have hwS : (permGL (Equiv.swap (0 : Fin 5) 1) : GL (Fin 5) F) ∈
      gramSU hF ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
    rw [← hHS, mem_unitarySU_iff hF]
    refine ⟨?_, permGL_unitary hF _⟩
    rw [det_permGL, Equiv.Perm.sign_swap hi01]
    have h2F : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    linear_combination -h2F
  obtain ⟨av, hav⟩ : ∃ av : (Fin 3 → Fin 5) → Multiplicative (Fin 3 → ZMod 25),
      ∀ v j, (Multiplicative.toAdd (av v) j).val = v j :=
    ⟨fun v => Multiplicative.ofAdd fun j => ((v j : ℕ) : ZMod 25),
      fun v j => ZMod.val_cast_of_lt (by have := (v j).isLt; omega)⟩
  refine ⟨φ, ⟨_, hwS⟩, ?_, fun c₀ hc₀ => ?_, fun a => ?_, fun a => ?_, av, ?_⟩
  · refine Subtype.ext ?_
    rw [Subgroup.coe_pow]
    change (permGL (Equiv.swap (0 : Fin 5) 1) : GL (Fin 5) F) ^ 2 = 1
    rw [← map_pow, sq, Equiv.swap_mul_self, map_one]
  · refine permGL_swap_not_mem_center hi01 hζ1 ?_
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c₀, hc₀.symm⟩
  ·
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hφ]
    change permGL (Equiv.swap (0 : Fin 5) 1) * diagHom 5 (expHom c hcp a) =
      diagHom 5 (expHom c hcp a) * permGL (Equiv.swap (0 : Fin 5) 1)
    have h01 : expHom c hcp a 0 = expHom c hcp a 1 := by
      rw [expHom_apply, expHom_apply]
      exact Finset.prod_congr rfl fun j _ => by rw [hc0, hc1]
    have hts : expHom c hcp a ∘ (Equiv.swap (0 : Fin 5) 1).symm = expHom c hcp a := by
      funext i
      rw [Function.comp_apply, Equiv.symm_swap]
      by_cases h0 : i = 0
      · rw [h0, Equiv.swap_apply_left, h01]
      · by_cases h1 : i = 1
        · rw [h1, Equiv.swap_apply_right, h01]
        · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
    have h1 := permGL_mul_diagHom_mul_inv (K := F) (Equiv.swap (0 : Fin 5) 1) (expHom c hcp a)
    rw [hts] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  ·
    refine ⟨∏ j, (ε⁻¹ ^ 5) ^ (Multiplicative.toAdd a j).val, ?_⟩
    rw [Subgroup.coe_pow, hφ, ← map_pow, ← hdiag]
    congr 1
    funext i
    rw [Pi.pow_apply, expHom_apply, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => by rw [pow_right_comm, hc5]
  ·
    intro v v' c₀ hc₀
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ, hφ, ← map_inv, ← map_mul, ← hdiag] at hc₀
    have hτ := diagHom_injective 5 hc₀
    funext j
    have e1 := congrFun hτ j.succ.succ
    have e0 := congrFun hτ 0
    simp only [Pi.mul_apply, Pi.inv_apply, mul_inv_eq_iff_eq_mul] at e1 e0
    rw [hratio, hratio, e0, mul_assoc, hav, hav] at e1
    exact Fin.ext (pow_injOn_Iio_orderOf (x := ζ) (by rw [Set.mem_Iio, hζo]; exact (v j).isLt)
      (by rw [Set.mem_Iio, hζo]; exact (v' j).isLt) (mul_left_cancel (mul_left_cancel e1)))

end Model

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

theorem not_dvd_of_qsnl (h : QSNL 5 S B T x D K) (hF : catalogIs (PSimple 5 K) (tyFUni 5))
    {m : ℕ} {F : Type} [Field F] (hFd : UnitaryFieldData 2 m F)
    (θ : ↥K ⧸ Subgroup.center ↥K ≃*
      primeFormP hFd ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) :
    ¬ 25 ∣ 2 ^ m + 1 := by
  intro h25
  obtain ⟨-, hDel, hDcard, -, -, hKcomp, hDK⟩ := h.cfg.std
  have hperf : Group.IsPerfect ↥K := ⟨hKcomp.2.2.1⟩
  have hZ := center_eq_bot_of_qsnl h hF
  obtain ⟨α, hαs, hα, -⟩ := exists_su5_cover hFd hperf θ
  obtain ⟨φ, w, hw2, hwc, hwφ, hφ5, av, hav⟩ := exists_torus_of_dvd hFd h25
  have hker : ∀ g, α g = 1 → ∃ c : Fˣ,
      (g : GL (Fin 5) F) = GeneralLinearGroup.scalar (Fin 5) c := fun g hg => by
    have h1 := hα g
    rw [hg, QuotientGroup.mk_one, map_one] at h1
    obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq_one_iff g).1 h1.symm
    exact ⟨c, hc⟩
  have hαc : ∀ g : gramSU hFd ((1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F),
      (∃ c : Fˣ, (g : GL (Fin 5) F) = GeneralLinearGroup.scalar (Fin 5) c) → α g = 1 := by
    rintro g ⟨c, hc⟩
    have h1 : α g ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.2 fun k => by
      obtain ⟨g', rfl⟩ := hαs k
      rw [← map_mul, ← map_mul]
      exact congrArg α (Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
        exact (commute_scalar c (g' : GL (Fin 5) F)).eq))
    rwa [hZ, Subgroup.mem_bot] at h1
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Multiplicative (Fin 3 → ZMod 25) →* Ω,
      ∀ a, ψ a = ((α (φ a) : ↥K) : Ω) := ⟨K.subtype.comp (α.comp φ), fun _ => rfl⟩
  have hψK : ∀ a, ψ a ∈ K := fun a => by
    rw [hψ]
    exact (α (φ a)).2
  have hψ5 : ∀ a, ψ a ^ 5 = 1 := fun a => by
    rw [hψ, ← Subgroup.coe_pow, ← map_pow, hαc _ (hφ5 a), Subgroup.coe_one]
  obtain ⟨u, hu⟩ : ∃ u : Ω, u = ((α w : ↥K) : Ω) := ⟨_, rfl⟩
  have hu2 : u ^ 2 = 1 := by
    rw [hu, ← Subgroup.coe_pow, ← map_pow, hw2, map_one, Subgroup.coe_one]
  have hu1 : u ≠ 1 := fun h1 => by
    rw [hu] at h1
    obtain ⟨c, hc⟩ := hker w (Subtype.ext h1)
    exact hwc c hc
  have hψu : ∀ a, ψ a * u = u * ψ a := fun a => by
    rw [hψ, hu, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hwφ a]
  have hUK : Subgroup.zpowers u ≤ K := Subgroup.zpowers_le.2 (by
    rw [hu]
    exact (α w).2)
  have hcardE : 5 ^ 3 ≤ Nat.card ψ.range := by
    calc 5 ^ 3 = Nat.card (Fin 3 → Fin 5) := by
          simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
      _ ≤ Nat.card ψ.range := Nat.card_le_card_of_injective
          (fun v => (⟨ψ (av v), av v, rfl⟩ : ψ.range)) fun v v' hvv => by
            have h1 : ψ (av v) = ψ (av v') := congrArg Subtype.val hvv
            rw [hψ, hψ] at h1
            obtain ⟨c, hc⟩ := hker (φ (av v) * (φ (av v'))⁻¹)
              (by rw [map_mul, map_inv, Subtype.ext h1, mul_inv_cancel])
            exact hav v v' c hc
  have hDC : D ≤ Subgroup.centralizer (K : Set Ω) := by
    rw [hDK]
    exact inf_le_right
  have hcomm : ∀ d ∈ D, ∀ k ∈ K, k * d = d * k := fun d hd k hk =>
    Subgroup.mem_centralizer_iff.1 (hDC hd) k hk
  have hE : IsElemAbelian 5 ψ.range := by
    refine ⟨⟨⟨fun e e' => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, rfl⟩⟩ := e
      obtain ⟨_, ⟨a', rfl⟩⟩ := e'
      apply Subtype.ext
      change ψ a * ψ a' = ψ a' * ψ a
      rw [← map_mul, ← map_mul, mul_comm a a']
    · rintro _ ⟨a, rfl⟩
      exact hψ5 a
  have hdisj : Disjoint ψ.range D := by
    rw [Subgroup.disjoint_def]
    rintro _ ⟨a, rfl⟩ hd
    have h1 : α (φ a) ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.2 fun l =>
      Subtype.ext (hcomm ((α (φ a) : ↥K) : Ω) (by rw [← hψ]; exact hd) l l.2)
    rw [hZ, Subgroup.mem_bot] at h1
    rw [hψ, h1, Subgroup.coe_one]
  have hDN : D ≤ Subgroup.normalizer (ψ.range : Set Ω) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun g hg => by
      obtain ⟨a, rfl⟩ := hg
      exact hcomm d hd _ (hψK a))
  have hel : IsElemAbelian 5 (ψ.range ⊔ D) := by
    refine IsElemAbelian.sup_of_commute hE hDel ?_
    rintro _ ⟨a, rfl⟩ d hd
    exact hcomm d hd _ (hψK a)
  have hU2 : IsPGroup 2 (Subgroup.zpowers u) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hu2)
  have hle : ψ.range ⊔ D ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup Ω) : Set Ω) := by
    refine sup_le ?_ fun d hd => Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hUK) (hDC hd))
    rintro _ ⟨a, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun g hg => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (Commute.zpow_left (show Commute u (ψ a) from (hψu a).symm) k).eq
  have h1 := card_le_pow_glaTwoLocalRank Nat.prime_five hel (Subgroup.zpowers_ne_bot.2 hu1) hU2
    hle
  have h2 : 5 ^ 3 * 5 ^ 2 ≤ 5 ^ 4 := calc
    5 ^ 3 * 5 ^ 2 ≤ Nat.card ψ.range * Nat.card D := by
        rw [hDcard]
        exact Nat.mul_le_mul_right _ hcardE
    _ = Nat.card (ψ.range ⊔ D : Subgroup Ω) :=
        (CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hDN hdisj).symm
    _ ≤ 5 ^ GLATwoLocalRank 5 Ω := h1
    _ ≤ Nat.card B := h.cfg.rank
    _ = 5 ^ 4 := card_eq_of_qsnl h hF
  norm_num at h2

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
