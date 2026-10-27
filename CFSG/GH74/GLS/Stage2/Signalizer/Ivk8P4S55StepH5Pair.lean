module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepHStmts
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Pair
public import CFSG.GH74.Generic.S3.Rank5
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Glue

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement MatrixGroups

section Algebra

theorem exists_hom_range {J Y' Q : Type*} [Group J] [Group Y'] [Group Q] (ι : J →* Y')
    (R : Subgroup Y') (hR : ι.range = R) (θ : J →* Q) (hθs : Function.Surjective θ)
    (hker : ∀ d : J, ι d = 1 → θ d = 1) : ∃ φ : ↥R →* Q, Function.Surjective φ := by
  subst hR
  have hle : ι.rangeRestrict.ker ≤ θ.ker := by
    intro d hd
    rw [MonoidHom.ker_rangeRestrict] at hd
    exact hker d hd
  refine ⟨ι.rangeRestrict.liftOfSurjective (MonoidHom.rangeRestrict_surjective ι) ⟨θ, hle⟩,
    fun q => ?_⟩
  obtain ⟨j, rfl⟩ := hθs q
  exact ⟨ι.rangeRestrict j, ι.rangeRestrict.liftOfRightInverse_comp_apply _ _ ⟨θ, hle⟩ j⟩

theorem statedSL2_center_sq {F : Type} [Field F] (c : ↥(StatedSL 2 F))
    (hc : ∀ g : ↥(StatedSL 2 F), g * c = c * g) : c ^ 2 = 1 := by
  set ε := specialLinearGroupEquivStatedSL 2 F with hε
  have hcen : ε.symm c ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply ε.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hc (ε g)
  have h2 : (ε.symm c) ^ 2 = 1 := by
    rcases CFSG.GH74.Generic.S3.sl2_center_eq hcen with h | h <;> rw [h] <;> simp [sq]
  have := congrArg ε h2
  simpa using this

end Algebra

section Pair

variable {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Module.Finite (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ}
  {K : Subgroup Γ} {a : Γ}

omit [Finite Γ] [Module.Finite (ZMod p) V] in
theorem pair_le_sup_zpowers {yh c k : Γ} (hyh : yh ∈ K) (hc : c ∈ centralizer (K : Set Γ))
    (hk : k ∈ K) : Subgroup.closure ({yh * c, k * (yh * c) * k⁻¹} : Set Γ) ≤ K ⊔ zpowers c := by
  have hcK : ∀ x ∈ K, x * c = c * x := fun x hx => Subgroup.mem_centralizer_iff.mp hc x hx
  rw [Subgroup.closure_le]
  have h1 : yh * c ∈ K ⊔ zpowers c :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hyh) (Subgroup.mem_sup_right (mem_zpowers c))
  have h2 : k * (yh * c) * k⁻¹ = (k * yh * k⁻¹) * c := by
    have : k * c * k⁻¹ = c := by rw [hcK k hk]; group
    calc k * (yh * c) * k⁻¹ = k * yh * (k⁻¹ * k) * c * k⁻¹ := by group
      _ = k * yh * k⁻¹ * (k * c * k⁻¹) := by group
      _ = (k * yh * k⁻¹) * c := by rw [this]
  rintro _ (rfl | rfl)
  · exact h1
  · rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hk hyh) (Subgroup.inv_mem _ hk)))
      (Subgroup.mem_sup_right (mem_zpowers c))

omit [Finite Γ] [Module.Finite (ZMod p) V] in
theorem Hyp89.pow_eq_one_of_odd_center (hf : Hyp89 p ρ K a) {yh c k : Γ} (hyh : yh ∈ K)
    (hcC : c ∈ centralizer (K : Set Γ)) (hac : a = yh * c) (hk : k ∈ K)
    (hodd : Odd (Nat.card (center ↥K))) {d : Γ}
    (hdJ : d ∈ Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)) (hdC : d ∈ centralizer (K : Set Γ)) :
    ∃ N : ℕ, Odd N ∧ d ^ N = 1 := by
  have hcK : ∀ x ∈ K, x * c = c * x := fun x hx => Subgroup.mem_centralizer_iff.mp hcC x hx
  have hcN : c ∈ normalizer (K : Set Γ) := Subgroup.centralizer_le_normalizer (K : Set Γ) hcC
  set n := Nat.card (center ↥K) with hn
  have hZ : ∀ x : Γ, x ∈ K → x ∈ centralizer (K : Set Γ) → x ^ n = 1 := by
    intro x hxK hxC
    have hmem : (⟨x, hxK⟩ : ↥K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
    have h1 : (⟨⟨x, hxK⟩, hmem⟩ : ↥(center ↥K)) ^ n = 1 := pow_card_eq_one'
    have h2 := congrArg (fun z : ↥(center ↥K) => ((z : ↥K) : Γ)) h1
    simpa using h2
  have hpow : a ^ p = 1 := hf.pow_prime
  have hcom : Commute yh c := hcK yh hyh
  have hcp : c ^ p = (yh ^ p)⁻¹ := by
    rw [hac, hcom.mul_pow] at hpow
    exact eq_inv_of_mul_eq_one_right hpow
  have hcpn : (c ^ p) ^ n = 1 := by
    refine hZ _ ?_ ?_
    · rw [hcp]; exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hyh p)
    · exact Subgroup.pow_mem _ hcC p
  subst hac
  obtain ⟨i, κ, hκK, hd⟩ := mem_sup_zpowers_decomp hcN (pair_le_sup_zpowers hyh hcC hk hdJ)
  have hκC : κ ∈ centralizer (K : Set Γ) := by
    have : κ = (c ^ i)⁻¹ * d := by rw [hd]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hcC i)) hdC
  have hκn : κ ^ n = 1 := hZ κ hκK hκC
  refine ⟨p * n, (hf.prime.odd_of_ne_two hf.odd).mul hodd, ?_⟩
  have hcomm : Commute (c ^ i) κ := (Commute.zpow_left (hcK κ hκK).symm i)
  have hcN1 : c ^ (p * n) = 1 := by rw [pow_mul]; exact hcpn
  have hκN : κ ^ (p * n) = 1 := by rw [mul_comm, pow_mul]; simp [hκn]
  rw [hd, hcomm.mul_pow, hκN, mul_one]
  have hord : (orderOf c : ℤ) ∣ i * ((p * n : ℕ) : ℤ) :=
    Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr (orderOf_dvd_of_pow_eq_one hcN1)) i
  have h1 := orderOf_dvd_iff_zpow_eq_one.mp hord
  rw [zpow_mul, zpow_natCast] at h1
  exact h1

theorem Hyp89.exists_pairSL2 (hf : Hyp89 p ρ K a) (hE2 : CrossE2) {y : ↥K ⧸ center ↥K}
    (hy : bAutN K a hf.norm = MulAut.conj y) : ∃ g : ↥K ⧸ center ↥K, PairSL2 p y g := by
  classical
  have hZ : center (↥K ⧸ center ↥K) = ⊥ := center_quot_eq_bot hf.quasi
  have hcen : ∀ z : ↥K ⧸ center ↥K, (∀ x, z * x = x * z) → z = 1 := by
    intro z hz
    have hz' : z ∈ center (↥K ⧸ center ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hz g).symm
    rw [hZ] at hz'
    exact hz'
  obtain ⟨k, hkK, -, -, N, hN, F, hFf, hFfin, hFp, ⟨e⟩⟩ := hE2 p Γ V ρ K a hf
  obtain ⟨yh, c, hyh, hcC, hac⟩ := hf.exists_inner_decomp hy
  obtain ⟨ι, hι1, hι2, hιker⟩ := exists_iota hf hy hcen hkK
  set g : ↥K ⧸ center ↥K := QuotientGroup.mk ⟨k, hkK⟩ with hg
  let θ := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hθs : Function.Surjective θ := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hrange : ι.range = Subgroup.closure ({y, g * y * g⁻¹} : Set (↥K ⧸ center ↥K)) := by
    rw [MonoidHom.range_eq_map, ← closure_pair_generates a (k * a * k⁻¹), MonoidHom.map_closure,
      Set.image_pair, hι1, hι2]
  have hDc : ∀ d : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)), ι d = 1 →
      ∀ j : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)), j * d = d * j := by
    intro d hd j
    have hdC : (d : Γ) ∈ centralizer (K : Set Γ) := (hιker d).mp hd
    have hdmem : (d : Γ) ∈
        Subgroup.closure ({(yh : Γ) * c, k * ((yh : Γ) * c) * k⁻¹} : Set Γ) := by
      rw [← hac]
      exact d.2
    have hjmem : (j : Γ) ∈
        Subgroup.closure ({(yh : Γ) * c, k * ((yh : Γ) * c) * k⁻¹} : Set Γ) := by
      rw [← hac]
      exact j.2
    have h1 := pair_central (K := K) yh.2 hcC hkK hdC hdmem
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (h1 hjmem))
  by_cases hD : ∀ d : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)), ι d = 1 → θ d = 1
  · obtain ⟨φ, hφ⟩ := exists_hom_range ι _ hrange θ hθs hD
    exact ⟨g, F, hFf, hFfin, hFp, Or.inl ⟨φ, hφ⟩⟩
  · push Not at hD
    obtain ⟨d, hd1, hdθ⟩ := hD
    have hθc : ∀ s : ↥(StatedSL 2 F), s * θ d = θ d * s := by
      intro s
      obtain ⟨j, rfl⟩ := hθs s
      rw [← map_mul, ← map_mul, hDc d hd1 j]
    have hsq : θ d ^ 2 = 1 := statedSL2_center_sq (θ d) hθc
    have hev : Even (Nat.card (center ↥K)) := by
      by_contra hne
      have hodd : Odd (Nat.card (center ↥K)) := Nat.not_even_iff_odd.mp hne
      obtain ⟨N', hN'odd, hN'⟩ := hf.pow_eq_one_of_odd_center yh.2 hcC hac hkK hodd
        (d := (d : Γ)) d.2 ((hιker d).mp hd1)
      apply hdθ
      have h1 : θ d ^ N' = 1 := by
        rw [← map_pow]
        have hdN : d ^ N' = 1 := Subtype.ext (by simpa using hN')
        rw [hdN, map_one]
      obtain ⟨m, hm⟩ := hN'odd
      rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul] at h1
      exact h1
    have hNoR : ¬ NoR 2 (↥K ⧸ center ↥K) := fun hN2 =>
      hN2 ↥K hf.quasi ⟨MulEquiv.refl _⟩ (even_iff_two_dvd.mp hev)
    let θb := (QuotientGroup.mk' (center ↥(StatedSL 2 F))).comp θ
    have hθbs : Function.Surjective θb := (QuotientGroup.mk'_surjective _).comp hθs
    have hker : ∀ d' : ↥(Subgroup.closure ({a, k * a * k⁻¹} : Set Γ)), ι d' = 1 → θb d' = 1 := by
      intro d' hd'
      show (QuotientGroup.mk (θ d') : ↥(StatedSL 2 F) ⧸ center ↥(StatedSL 2 F)) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro s
      obtain ⟨j, rfl⟩ := hθs s
      rw [← map_mul, ← map_mul, hDc d' hd' j]
    obtain ⟨φ, hφ⟩ := exists_hom_range ι _ hrange θb hθbs hker
    exact ⟨g, F, hFf, hFfin, hFp, Or.inr ⟨hNoR, φ, hφ⟩⟩

end Pair

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
