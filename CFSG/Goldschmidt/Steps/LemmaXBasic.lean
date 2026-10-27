module

public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.FusionDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace LemmaX

variable {G : Type*} [Group G]

theorem mem_map_conj_inv_iff {M : Subgroup G} {g t : G} :
    t ∈ M.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * t * g⁻¹ ∈ M := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hm
  · intro h
    exact ⟨g * t * g⁻¹, h, by simp [mul_assoc]⟩

theorem mem_map_conj_iff {M : Subgroup G} {g t : G} :
    t ∈ M.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * t * g ∈ M := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hm
  · intro h
    exact ⟨g⁻¹ * t * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem stronglyClosed_map_conj {A S : Subgroup G} (hcl : fusionStronglyClosed (A : Set G) S)
    (k : G) : fusionStronglyClosed ((A.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G)
      (S.map (MulAut.conj k).toMonoidHom) := by
  intro a ha g hg
  rw [SetLike.mem_coe, mem_map_conj_iff] at ha
  rw [mem_map_conj_iff] at hg
  rw [SetLike.mem_coe, mem_map_conj_iff]
  have e : k⁻¹ * (g⁻¹ * a * g) * k =
      (k⁻¹ * g * k)⁻¹ * (k⁻¹ * a * k) * (k⁻¹ * g * k) := by group
  rw [e] at hg ⊢
  exact hcl _ ha _ hg

theorem not_mem_of_odd_card {K : Subgroup G} (hK : Odd (Nat.card K)) {t : G}
    (ht : orderOf t = 2) : t ∉ K := by
  intro htK
  have h2 : 2 ∣ Nat.card K := ht ▸ Subgroup.orderOf_dvd_natCard K htK
  exact (Nat.not_even_iff_odd.2 hK) (even_iff_two_dvd.2 h2)

theorem exists_mem_orderOf_eq_two [Finite G] {K : Subgroup G} (hK : ¬ Odd (Nat.card K)) :
    ∃ t ∈ K, orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := K) 2
    (Nat.not_odd_iff_even.1 hK).two_dvd
  exact ⟨t, t.2, (Subgroup.orderOf_coe t).trans ht⟩

theorem isPGroup_zpowers_of_pow_eq_one {t : G} {n : ℕ} (ht : t ^ 2 ^ n = 1) :
    IsPGroup 2 (Subgroup.zpowers t) := by
  rintro ⟨s, hs⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  refine ⟨n, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]

theorem exists_conj_mem_sylow [Finite G] (P : Sylow 2 G) {t : G} {n : ℕ} (ht : t ^ 2 ^ n = 1) :
    ∃ g : G, g * t * g⁻¹ ∈ (P : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := (isPGroup_zpowers_of_pow_eq_one ht).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R P
  refine ⟨g, ?_⟩
  rw [← hg]
  exact ⟨t, hR (Subgroup.mem_zpowers t), by simp [MulAut.conj_apply]⟩

theorem isStronglyEmbeddedOrder_iff (M : Subgroup G) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M ↔ fusionStronglyEmbedded M := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun g hg => ?_⟩
    exact h3 g⁻¹ (fun h => hg (by simpa using M.inv_mem h))
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun g hg => ?_⟩
    have := h3 g⁻¹ (fun h => hg (by simpa using M.inv_mem h))
    simpa using this

theorem fusionStronglyEmbedded_comap [Finite G] {G' : Type*} [Group G'] [Finite G']
    (f : G →* G') (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    {M' : Subgroup G'} (hM' : fusionStronglyEmbedded M') :
    fusionStronglyEmbedded (M'.comap f) := by
  obtain ⟨h1, h2, h3⟩ := hM'
  refine ⟨?_, ?_, fun g hg => ?_⟩
  · intro htop
    apply h1
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hf x
    have : y ∈ M'.comap f := htop ▸ Subgroup.mem_top y
    exact this
  · obtain ⟨x', hx', hx'2⟩ := exists_mem_orderOf_eq_two (K := M') (Nat.not_odd_iff_even.2 h2)
    obtain ⟨x, rfl⟩ := hf x'
    have hx : x ∈ M'.comap f := hx'
    have hdvd : 2 ∣ orderOf x := hx'2 ▸ orderOf_map_dvd f x
    exact even_iff_two_dvd.2 (hdvd.trans (Subgroup.orderOf_dvd_natCard _ hx))
  · by_contra hodd
    obtain ⟨x, hx, hx2⟩ := exists_mem_orderOf_eq_two hodd
    obtain ⟨hxM, hxg⟩ := Subgroup.mem_inf.1 hx
    have hgx : g * x * g⁻¹ ∈ M'.comap f := mem_map_conj_inv_iff.1 hxg
    by_cases hfx : f x = 1
    · exact not_mem_of_odd_card hker hx2 (MonoidHom.mem_ker.2 hfx)
    · have hfx2 : orderOf (f x) = 2 := by
        have hd : orderOf (f x) ∣ 2 := hx2 ▸ orderOf_map_dvd f x
        rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hfx
        · exact h
      apply not_mem_of_odd_card (h3 (f g) hg) hfx2
      refine Subgroup.mem_inf.2 ⟨hxM, mem_map_conj_inv_iff.2 ?_⟩
      have : f (g * x * g⁻¹) ∈ M' := hgx
      simpa [map_mul, map_inv] using this

theorem exists_pow_conj_eq_mul {t o : G} (ht : t * t = 1) (hto : t * o * (t * o) = 1)
    (ho : Odd (orderOf o)) : ∃ a : ℕ, t * o = (o ^ a)⁻¹ * t * o ^ a := by
  obtain ⟨k, hk⟩ := ho
  refine ⟨k + 1, ?_⟩
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : t * o * t = o⁻¹ := by
    have h : t * o * t * o = 1 := by simpa [mul_assoc] using hto
    calc t * o * t = t * o * t * o * o⁻¹ := by group
      _ = o⁻¹ := by rw [h, one_mul]
  have h2 : ∀ n : ℕ, t * o ^ n * t = (o ^ n)⁻¹ := by
    intro n
    have h3 : (t * o * t⁻¹) ^ n = t * o ^ n * t⁻¹ := conj_pow
    rw [ht', h1, inv_pow] at h3
    exact h3.symm
  have hpow : o ^ (k + 1) * o ^ (k + 1) = o := by
    rw [← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk,
      pow_orderOf_eq_one, one_mul]
  rw [← h2 (k + 1)]
  have e : t * o ^ (k + 1) * t * t * o ^ (k + 1) = t * o ^ (k + 1) * (t * t) * o ^ (k + 1) := by
    group
  rw [e, ht, mul_one, mul_assoc, hpow]

theorem le_of_forall_inf_centralizer_le [Finite G] {E N J : Subgroup G}
    (hEcomm : IsMulCommutative E) (hEexp : ∀ x ∈ E, x ^ 2 = 1) (hE4 : 4 ≤ Nat.card E)
    (hEN : E ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N))
    (h : ∀ e ∈ E, e ≠ 1 → N ⊓ Subgroup.centralizer ({e} : Set G) ≤ J) : N ≤ J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsElementaryAbelian 2 E :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hEexp x x.2) }
  let _ : MulDistribMulAction E N := Subgroup.conjMulDistribMulActionOfLeNormalizer E N hEN
  have hcop : ¬ 2 ∣ Nat.card N := fun h2 =>
    (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := E) (H := N)
    (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hE4) hcop
  have hle : ∀ a : E, a ≠ 1 →
      CFSG.fixedPointSubgroup (Subgroup.zpowers a) N ≤ J.subgroupOf N := by
    intro a ha x hx
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hx
    have hxa : ((a : G) * x * (a : G)⁻¹) = x := congrArg Subtype.val hx
    rw [Subgroup.mem_subgroupOf]
    refine h a a.2 (fun h1 => ha (Subtype.ext h1)) (Subgroup.mem_inf.2 ⟨x.2, ?_⟩)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x : G) * a = (a : G) * x * (a : G)⁻¹ * a := by rw [hxa]
      _ = a * x := by group
  have htop : (⊤ : Subgroup N) ≤ J.subgroupOf N := by
    rw [← hgen]
    exact iSup₂_le fun a ha => hle a ha
  intro x hx
  exact Subgroup.mem_subgroupOf.1 (htop (Subgroup.mem_top ⟨x, hx⟩))

theorem card_le_card_inf_centralizer_sq [Finite G] {U : Subgroup G} (hUab : IsMulCommutative U)
    (hUexp : ∀ u ∈ U, u ^ 2 = 1) {t : G} (htU : t ∈ Subgroup.normalizer (U : Set G))
    (ht : t * t = 1) :
    Nat.card U ≤ Nat.card (U ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hUab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hconj : ∀ u ∈ U, t * u * t⁻¹ ∈ U := fun u hu => (Subgroup.mem_normalizer_iff.1 htU u).1 hu
  have htt : ∀ u : G, t * (t * u * t⁻¹) * t⁻¹ = u := by
    intro u
    have e : t * (t * u * t⁻¹) * t⁻¹ = (t * t) * u * (t * t)⁻¹ := by group
    rw [e, ht, one_mul, inv_one, mul_one]
  have hinv : ∀ u ∈ U, u⁻¹ = u := fun u hu =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hUexp u hu)
  let φ : U →* U :=
    { toFun := fun u => ⟨(u : G) * (t * u * t⁻¹), U.mul_mem u.2 (hconj u u.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun u v => by
        apply Subtype.ext
        show ((u : G) * v) * (t * (u * v) * t⁻¹) = (u * (t * u * t⁻¹)) * (v * (t * v * t⁻¹))
        have h1 : (v : G) * (t * u * t⁻¹) = (t * u * t⁻¹) * v :=
          hcomm _ v.2 _ (hconj u u.2)
        calc ((u : G) * v) * (t * (u * v) * t⁻¹)
            = (u : G) * (v * (t * u * t⁻¹)) * (t * v * t⁻¹) := by group
          _ = (u * (t * u * t⁻¹)) * (v * (t * v * t⁻¹)) := by rw [h1]; group }
  set K : Subgroup U := (U ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf U with hK
  have hmemK : ∀ w : U, t * (w : G) * t⁻¹ = w → w ∈ K := by
    intro w hw
    rw [hK, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.2 ⟨w.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (w : G) * t = t * w * t⁻¹ * t := by rw [hw]
      _ = t * w := by group
  have hker : φ.ker ≤ K := by
    intro u hu
    apply hmemK
    have h1 : (u : G) * (t * u * t⁻¹) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hu)
    have h2 : t * (u : G) * t⁻¹ = (u : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2, hinv _ u.2]
  have hrange : φ.range ≤ K := by
    rintro _ ⟨u, rfl⟩
    apply hmemK
    show t * ((u : G) * (t * u * t⁻¹)) * t⁻¹ = (u : G) * (t * u * t⁻¹)
    calc t * ((u : G) * (t * u * t⁻¹)) * t⁻¹ = (t * u * t⁻¹) * (t * (t * u * t⁻¹) * t⁻¹) := by
          group
      _ = (t * u * t⁻¹) * u := by rw [htt]
      _ = (u : G) * (t * u * t⁻¹) := (hcomm _ u.2 _ (hconj u u.2)).symm
  have hcardK : Nat.card K = Nat.card (U ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at h
  calc Nat.card U = Nat.card φ.ker * Nat.card φ.range := h.symm
    _ ≤ Nat.card K * Nat.card K :=
        Nat.mul_le_mul (Subgroup.card_le_of_le hker) (Subgroup.card_le_of_le hrange)
    _ = _ := by rw [hcardK, sq]

end LemmaX

end CFSG.Goldschmidt
