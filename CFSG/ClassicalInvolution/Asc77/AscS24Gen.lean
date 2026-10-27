module

public import CFSG.ClassicalInvolution.Asc77.AscS24Pair
public import CFSG.ClassicalInvolution.Asc77.AscT7C2RChain

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (classicalInvolutionOddCore IsElemAbelian)
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem frame_mul_conj_ne : ∀ a ∈ S4.swaps4, ∀ b ∈ S4.swaps4, ∀ c ∈ S4.swaps4, a ≠ b →
    a * b = b * a → a * c ≠ c * a → a * b * c * (a * b)⁻¹ ≠ c := by
  decide

namespace Ctx


variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u g : G}
  (C : Ctx p f Ω K K' W S R R' z u g)

include C

theorem conjSub_rt_J_ne [IsSimpleGroup G] :
    conjSub (C.D.F.ρ.r * C.D.F.ρ'.r) (conjSub g⁻¹ K) ≠ conjSub g⁻¹ K := by
  have hst := C.hs.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst C.hd.hW
  obtain ⟨e, he⟩ := T7D.exists_swap_equiv C.hs C.hd.hW C.hd.hS4
  have hrN := C.D.F.ρ.r_mem_normalizer
  have htN := C.D.F.ρ'.r_mem_normalizer
  have hn : C.D.F.ρ.r * C.D.F.ρ'.r ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ hrN htN
  intro h
  have hσK : (T7D.conjRep hΩ hn C.D.F.ρ₃).K = C.D.F.ρ₃.K := by
    show conjSub (C.D.F.ρ.r * C.D.F.ρ'.r) C.D.F.ρ₃.K = C.D.F.ρ₃.K
    rw [C.hJ]
    exact h
  have himg := c.img_eq_of_K_eq _ _ hσK
  rw [T7D.conjRep_img, Thompson.piG_mul hrN htN] at himg
  have hQ : T7D.imgQ C.D.F.ρ * T7D.imgQ C.D.F.ρ' * T7D.imgQ C.D.F.ρ₃ *
      (T7D.imgQ C.D.F.ρ * T7D.imgQ C.D.F.ρ')⁻¹ = T7D.imgQ C.D.F.ρ₃ := Subtype.ext himg
  have hne : C.D.F.ρ.K ≠ C.D.F.ρ'.K := by
    rw [C.hK, C.hK']
    exact C.hs.hne.symm
  have hab : T7D.imgQ C.D.F.ρ ≠ T7D.imgQ C.D.F.ρ' := fun h =>
    hne (c.K_eq_of_img_eq _ _ (congrArg Subtype.val h))
  have hcomm : T7D.imgQ C.D.F.ρ * T7D.imgQ C.D.F.ρ' = T7D.imgQ C.D.F.ρ' * T7D.imgQ C.D.F.ρ :=
    Subtype.ext (c.comm_of_omega _ _ C.D.F.hnbr)
  have hac : T7D.imgQ C.D.F.ρ * T7D.imgQ C.D.F.ρ₃ ≠ T7D.imgQ C.D.F.ρ₃ * T7D.imgQ C.D.F.ρ :=
    fun h => C.D.F.hn₁ (c.omega_of_comm _ _ C.D.F.hne₁ (congrArg Subtype.val h))
  refine frame_mul_conj_ne (e (T7D.imgQ C.D.F.ρ)) (S4.mem_swaps4_of_mem he (T7D.imgQ_mem _))
    (e (T7D.imgQ C.D.F.ρ')) (S4.mem_swaps4_of_mem he (T7D.imgQ_mem _))
    (e (T7D.imgQ C.D.F.ρ₃)) (S4.mem_swaps4_of_mem he (T7D.imgQ_mem _))
    (fun h => hab (e.injective h)) (by rw [← map_mul, ← map_mul, hcomm])
    (fun h => hac (e.injective (by rw [map_mul, map_mul, h]))) ?_
  have := congrArg e hQ
  simpa only [map_mul, map_inv] using this

theorem hs_J : Hyp23Setting p f Ω (conjSub g⁻¹ K) (conjSub g⁻¹ K') u := by
  have := C.hs.conj g⁻¹
  rwa [inv_inv, C.hg] at this

theorem twin_J_le [IsSimpleGroup G] : conjSub g⁻¹ K' ≤ K ⊔ conjSub g⁻¹ K ⊔ K' := by
  have hst := C.hs.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hsJ := C.hs_J
  set n := C.D.F.ρ.r * C.D.F.ρ'.r with hn
  have hnu : n * u * n⁻¹ = u := by
    calc n * u * n⁻¹ = C.D.F.ρ.r * (C.D.F.ρ'.r * u * C.D.F.ρ'.r⁻¹) * C.D.F.ρ.r⁻¹ := by
          rw [hn]; group
      _ = u := by rw [C.conj_t_u, C.conj_r_uz]
  have hmem : conjSub n (conjSub g⁻¹ K) ∈ twinSet Ω (conjSub g⁻¹ K) := by
    refine ⟨hΩ.conjInvariant n _ C.J_mem, u, hsJ.hz, ?_⟩
    have h1 := hsJ.hz.conj n
    rwa [hnu] at h1
  rw [hsJ.twinSet_eq] at hmem
  obtain h | h := hmem
  · exact absurd h C.conjSub_rt_J_ne
  · have h' : conjSub n (conjSub g⁻¹ K) = conjSub g⁻¹ K' := h
    rw [← h']
    intro x hx
    rw [mem_conjSub_iff] at hx
    have hnX : n ∈ K ⊔ conjSub g⁻¹ K ⊔ K' :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left C.r_mem_K))
        (Subgroup.mem_sup_right C.t_mem_K')
    have e1 : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnX
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hx))) (Subgroup.inv_mem _ hnX)

theorem conj_le_of_centralizes [IsSimpleGroup G] {c₀ : G} (hz : c₀ * z = z * c₀)
    (hu : c₀ * u = u * c₀) :
    conjSub c₀ (K ⊔ conjSub g⁻¹ K ⊔ K') ≤ K ⊔ conjSub g⁻¹ K ⊔ K' := by
  have hst := C.hs.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hsJ := C.hs_J
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet C.hs.hz C.hs.hK'
  have hcz : c₀ * z * c₀⁻¹ = z := by rw [hz]; group
  have hcu : c₀ * u * c₀⁻¹ = u := by rw [hu]; group
  have hKt : conjSub c₀ K ∈ twinSet Ω K := by
    refine ⟨hΩ.conjInvariant _ _ hst.mem, z, C.hs.hz, ?_⟩
    have := C.hs.hz.conj c₀
    rwa [hcz] at this
  have hK't : conjSub c₀ K' ∈ twinSet Ω K := by
    refine ⟨hΩ.conjInvariant _ _ C.hs.hK'.1, z, C.hs.hz, ?_⟩
    have := hz'.conj c₀
    rwa [hcz] at this
  have hJt : conjSub c₀ (conjSub g⁻¹ K) ∈ twinSet Ω (conjSub g⁻¹ K) := by
    refine ⟨hΩ.conjInvariant _ _ C.J_mem, u, hsJ.hz, ?_⟩
    have := hsJ.hz.conj c₀
    rwa [hcu] at this
  rw [C.hs.twinSet_eq] at hKt hK't
  rw [hsJ.twinSet_eq] at hJt
  have hJ' := C.twin_J_le
  have hKK : ∀ M : Subgroup G, M ∈ ({K, K'} : Set (Subgroup G)) →
      M ≤ K ⊔ conjSub g⁻¹ K ⊔ K' := by
    rintro M (rfl | rfl)
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right
  have hJJ : ∀ M : Subgroup G, M ∈ ({conjSub g⁻¹ K, conjSub g⁻¹ K'} : Set (Subgroup G)) →
      M ≤ K ⊔ conjSub g⁻¹ K ⊔ K' := by
    rintro M (rfl | rfl)
    · exact le_sup_right.trans le_sup_left
    · exact hJ'
  rw [T7C2.conjSub_sup, T7C2.conjSub_sup]
  exact sup_le (sup_le (hKK _ hKt) (hJJ _ hJt)) (hKK _ hK't)

theorem sup3_eq_top [IsSimpleGroup G] : K ⊔ conjSub g⁻¹ K ⊔ K' = ⊤ := by
  set X₀ := K ⊔ conjSub g⁻¹ K ⊔ K' with hX₀
  have hnorm_of : ∀ c : G, conjSub c X₀ ≤ X₀ → conjSub c⁻¹ X₀ ≤ X₀ →
      c ∈ Subgroup.normalizer (X₀ : Set G) := by
    intro c h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact h1 (conj_mem_conjSub hx)
    · intro hx
      have := h2 (conj_mem_conjSub (n := c⁻¹) hx)
      simpa [mul_assoc] using this
  have hZU : ∀ c₀ : G, c₀ * z = z * c₀ → c₀ * u = u * c₀ →
      c₀ ∈ Subgroup.normalizer (X₀ : Set G) := by
    intro c₀ hz hu
    have hz' : c₀⁻¹ * z = z * c₀⁻¹ := by
      calc c₀⁻¹ * z = c₀⁻¹ * (z * c₀) * c₀⁻¹ := by group
        _ = c₀⁻¹ * (c₀ * z) * c₀⁻¹ := by rw [hz]
        _ = z * c₀⁻¹ := by group
    have hu' : c₀⁻¹ * u = u * c₀⁻¹ := by
      calc c₀⁻¹ * u = c₀⁻¹ * (u * c₀) * c₀⁻¹ := by group
        _ = c₀⁻¹ * (c₀ * u) * c₀⁻¹ := by rw [hu]
        _ = u * c₀⁻¹ := by group
    exact hnorm_of c₀ (C.conj_le_of_centralizes hz hu) (C.conj_le_of_centralizes hz' hu')
  have hKK'X : K ⊔ K' ≤ X₀ := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (X₀ : Set G) := by
    intro c hc
    obtain ⟨q, hq, c₀, hc₀, hcomm, rfl⟩ :=
      T7K.centralizer_eq_sup_mul C.hs C.hd.hu.1 C.u_ne_one C.u_ne_z C.u_sq hc
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer (hKK'X hq))
      (hZU c₀ (Subgroup.mem_centralizer_singleton_iff.mp hc₀) hcomm)
  set n := C.D.F.ρ.r * C.D.F.ρ₃.r with hn
  have hnz : n * z * n⁻¹ = u := by
    calc n * z * n⁻¹ = C.D.F.ρ.r * (C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹) * C.D.F.ρ.r⁻¹ := by
          rw [hn]; group
      _ = u := by rw [C.conj_s_z, C.conj_r_uz]
  have hnX : n ∈ X₀ := Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left C.r_mem_K))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right C.s_mem_J))
  have hCu : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (X₀ : Set G) := by
    intro c hc
    have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have h1 : n⁻¹ * c * n ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc n⁻¹ * c * n * z = n⁻¹ * c * (n * z * n⁻¹) * n := by group
        _ = n⁻¹ * (c * u) * n := by rw [hnz]; group
        _ = n⁻¹ * (u * c) * n := by rw [hcu]
        _ = n⁻¹ * (n * z * n⁻¹) * c * n := by rw [hnz]; group
        _ = z * (n⁻¹ * c * n) := by group
    have h2 := hCz h1
    have e1 : c = n * (n⁻¹ * c * n) * n⁻¹ := by group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer hnX) h2)
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hnX))
  have htop : Subgroup.normalizer (X₀ : Set G) = ⊤ := by
    rw [eq_top_iff, ← sup_centralizer_eq_top_of C.hs C.hd]
    exact sup_le hCu hCz
  have hN : X₀.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases Subgroup.Normal.eq_bot_or_eq_top X₀ with h | h
  · exfalso
    have hz : z ∈ X₀ := Subgroup.mem_sup_left (Subgroup.mem_sup_left C.hs.hz.mem)
    rw [h] at hz
    exact C.hs.hz.ne_one hz
  · exact h

theorem commutes_twin [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) :
    Commutes K K' := by
  have hst := C.hs.stand
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet C.hs.hz C.hs.hK'
  have h := hst.hyp.comm_le_oddCore_of_twin hst.mem C.hs.hK'.1 C.hs.hne.symm C.hs.hz hz'
  rw [C.oddCoreOf_K_eq_bot hZ hL, bot_inf_eq] at h
  intro x hx y hy
  have := h (Subgroup.commutator_mem_commutator hx hy)
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp this)

end Ctx

end CFSG.ClassicalInvolution.Asc77.S24
