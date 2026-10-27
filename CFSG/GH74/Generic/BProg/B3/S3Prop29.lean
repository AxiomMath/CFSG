module

public import CFSG.GH74.Generic.BProg.B3.S3Prop29Bal
public import CFSG.GH74.Generic.BProg.B3.S3Rk1Basic
public import CFSG.GH74.Generic.BProg.B3.FalseCtxS45Comp

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.TwoThin CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

namespace S3Prop29

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem xbar_central {x : G} (hx : x ∈ centralizer ({x} : Set G))
    (l : barQ ↥(centralizer ({x} : Set G))) :
    barMk ↥(centralizer ({x} : Set G)) ⟨x, hx⟩ * l = l * barMk ↥(centralizer ({x} : Set G)) ⟨x, hx⟩ := by
  obtain ⟨c, rfl⟩ := barMk_surjective l
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_singleton_iff.1 c.2).symm

theorem locBal32_bar {x : G} {K A E B' : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K))
    (hEK : E ≤ K) (hAE : A = E ⊔ zpowers x) (hx : orderOf x = 2)
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hB'A : B' ≤ A) :
    IsLocBal32 (↥(PumpCalc.bar x K) ⧸ center ↥(PumpCalc.bar x K))
      (((PumpCalc.bar x B').subgroupOf
        (normalizer ((PumpCalc.bar x K : Subgroup (barQ ↥(centralizer ({x} : Set G)))) :
          Set (barQ ↥(centralizer ({x} : Set G)))))).map (rhoL (PumpCalc.bar x K))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨e, he⟩ := S3Prop29Bal.exists_canonical_equiv hK
  set N : Subgroup ↥K := pPrimeCore 2 ↥K with hN
  let ψ : ↥K →* ↥K ⧸ N := QuotientGroup.mk' N
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK h3
  let φ : ((↥K ⧸ N) ⧸ center (↥K ⧸ N)) ≃* (↥(PumpCalc.bar x K) ⧸ center ↥(PumpCalc.bar x K)) :=
    QuotientGroup.congr (center (↥K ⧸ N)) (center ↥(PumpCalc.bar x K)) e
      (CFSG.LieType.Universal.Unitary.map_center_mulEquiv e)
  have hφ : ∀ k : ↥K ⧸ N, φ (QuotientGroup.mk k) = QuotientGroup.mk (e k) := fun k => rfl
  set Ab : Subgroup (↥K ⧸ N) := (E.subgroupOf K).map ψ with hAb
  have hEel' : CFSG.IsElementaryAbelian 2 ↥(E.subgroupOf K) := IsElementaryAbelian.subgroupOf hEK
  have hAbe : CFSG.IsElementaryAbelian 2 ↥Ab := IsElementaryAbelian.map ψ
  refine S3Prop29Bal.locBal32_of_equiv' (PumpCalc.bar x K) e φ hφ (Ab := Ab)
    (fun B₀ hB₀ => S3Prop29Bal.locBal32_of_le_range h3 hZ hAbe B₀ hB₀) ?_
  intro m hmB
  obtain ⟨⟨d, hdC⟩, hdB, hmd⟩ := hmB
  have hdB' : d ∈ B' := Subgroup.mem_subgroupOf.1 hdB
  have hdA : d ∈ A := hB'A hdB'
  obtain ⟨e₀, he₀, hd⟩ := S3Rk1Basic.decomp_A hKC hEK hAE hx hdA
  have he₀K : e₀ ∈ K := hEK he₀
  have he₀C : e₀ ∈ centralizer ({x} : Set G) := hKC he₀K
  have hmem₀ : barMk ↥(centralizer ({x} : Set G)) ⟨e₀, he₀C⟩ ∈ PumpCalc.bar x K :=
    ⟨⟨e₀, he₀C⟩, Subgroup.mem_subgroupOf.2 he₀K, rfl⟩
  have hLN : barMk ↥(centralizer ({x} : Set G)) ⟨e₀, he₀C⟩ ∈ normalizer ((PumpCalc.bar x K : Subgroup (barQ ↥(centralizer ({x} : Set G)))) : Set _) :=
    Subgroup.le_normalizer hmem₀
  set m₀ : ↥(normalizer ((PumpCalc.bar x K : Subgroup (barQ ↥(centralizer ({x} : Set G)))) : Set (barQ ↥(centralizer ({x} : Set G))))) :=
    ⟨barMk ↥(centralizer ({x} : Set G)) ⟨e₀, he₀C⟩, hLN⟩ with hm₀
  have hr₀ : rhoL (PumpCalc.bar x K) m₀ = MulAut.conj (φ (QuotientGroup.mk (ψ ⟨e₀, he₀K⟩))) := by
    rw [S3Prop29Bal.rhoL_eq_conj m₀ hmem₀, hφ]
    congr 1
    show _ = QuotientGroup.mk (e (QuotientGroup.mk ⟨e₀, he₀K⟩))
    congr 1
    apply Subtype.ext
    rw [he e₀ he₀K]
  refine ⟨ψ ⟨e₀, he₀K⟩, ⟨⟨e₀, he₀K⟩, Subgroup.mem_subgroupOf.2 he₀, rfl⟩, ?_⟩
  rcases hd with hd | hd
  · have hsub : (⟨d, hdC⟩ : ↥(centralizer ({x} : Set G))) = ⟨e₀, he₀C⟩ := Subtype.ext hd
    have hmeq : m = m₀ := by
      apply Subtype.ext
      rw [← hmd, hsub]
    rw [hmeq, hr₀]
  · have hxN : barMk ↥(centralizer ({x} : Set G)) ⟨x, hxC⟩ ∈ normalizer ((PumpCalc.bar x K : Subgroup (barQ ↥(centralizer ({x} : Set G)))) : Set _) := by
      refine Subgroup.mem_normalizer_iff.2 fun l => ?_
      constructor
      · intro hl
        have : barMk ↥(centralizer ({x} : Set G)) ⟨x, hxC⟩ * l * (barMk ↥(centralizer ({x} : Set G)) ⟨x, hxC⟩)⁻¹ = l := by
          rw [xbar_central hxC l]; group
        rw [this]; exact hl
      · intro hl
        have : barMk ↥(centralizer ({x} : Set G)) ⟨x, hxC⟩ * l * (barMk ↥(centralizer ({x} : Set G)) ⟨x, hxC⟩)⁻¹ = l := by
          rw [xbar_central hxC l]; group
        rw [this] at hl; exact hl
    set mx : ↥(normalizer ((PumpCalc.bar x K : Subgroup (barQ ↥(centralizer ({x} : Set G)))) : Set (barQ ↥(centralizer ({x} : Set G))))) :=
      ⟨barMk ↥(centralizer ({x} : Set G)) ⟨x, hxC⟩, hxN⟩ with hmx
    have hsub : (⟨d, hdC⟩ : ↥(centralizer ({x} : Set G))) = ⟨e₀, he₀C⟩ * ⟨x, hxC⟩ :=
      Subtype.ext hd
    have hmeq : m = m₀ * mx := by
      apply Subtype.ext
      rw [← hmd, hsub, map_mul]
      rfl
    rw [hmeq, S3Prop29Bal.rhoL_mul_of_centralizes m₀ mx (fun l _ => xbar_central hxC l), hr₀]

theorem false_of_obs_K {x : G} {K A D : Subgroup G} (hc : Ctx21 G x K A x D K)
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) : False := by
  classical
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4, hxK⟩ := S3Rk1Basic.exists_E hc.circ hc.src h3
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := S3Rk1Basic.pcomp_of_circ hc.circ
  have hx2 : orderOf x = 2 := S3Rk1Basic.orderOf_x_of_circ hc.circ
  have hAN : A ≤ normalizer (K : Set G) := S3Rk1Basic.A_le_normalizer hK.1 hEK hAE hx2
  obtain ⟨hDA, hDel, hDrk⟩ := hc.obs.D_le
  rcases hc.obs_cases with h2 | ⟨h1', -⟩ | ⟨-, e', he'A, he'N, -⟩
  · exact hc.obs.not_locBal32_rank2 h2 (locBal32_bar hK h3 hEK hAE hx2 hEel hDA)
  · exact hc.obs.not_locBal32_rank1 h1' hAN (locBal32_bar hK h3 hEK hAE hx2 hEel le_rfl)
  · exact he'N (hAN he'A)

theorem false_of_obs_ne {x : G} {K A D J : Subgroup G} (hc : Ctx21 G x K A x D J)
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K))
    (hcomm : ⁅PumpCalc.bar x J, PumpCalc.bar x K⁆ = ⊥) : False := by
  classical
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4, hxK⟩ := S3Rk1Basic.exists_E hc.circ hc.src h3
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := S3Rk1Basic.pcomp_of_circ hc.circ
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hx2 : orderOf x = 2 := S3Rk1Basic.orderOf_x_of_circ hc.circ
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨hDA, hDel, hDrk⟩ := hc.obs.D_le
  obtain ⟨d, hdD, hd1⟩ := Th2Sig6.exists_ne_one_of_card (k := pRank 2 ↥D) hDrk
    (C3.Layer1.Back.card_eq_two_pow_pRank hDel)
  have hdA : d ∈ A := hDA hdD
  have hdY : d ∈ centralizer ({x} : Set G) := hc.src.1 hdA
  refine hc.obs.D_faith d hdD hd1 (ObsPump.mem_cSec_of_bar_comm hc.obs.comp hdY fun l hl => ?_)
  have hcK : ∀ k ∈ K, ∀ (hk : k ∈ centralizer ({x} : Set G)),
      barMk ↥(centralizer ({x} : Set G)) ⟨k, hk⟩ * l = l * barMk ↥(centralizer ({x} : Set G)) ⟨k, hk⟩ := by
    intro k hkK hk
    have hqb : barMk ↥(centralizer ({x} : Set G)) ⟨k, hk⟩ ∈ PumpCalc.bar x K :=
      ⟨⟨k, hk⟩, Subgroup.mem_subgroupOf.mpr hkK, rfl⟩
    have hl' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hl
    exact Subgroup.mem_centralizer_iff.mp hl' _ hqb
  obtain ⟨e₀, he₀, hd⟩ := S3Rk1Basic.decomp_A hKC hEK hAE hx2 hdA
  have he₀C : e₀ ∈ centralizer ({x} : Set G) := hKC (hEK he₀)
  rcases hd with hd | hd
  · have : (⟨d, hdY⟩ : ↥(centralizer ({x} : Set G))) = ⟨e₀, he₀C⟩ := Subtype.ext hd
    rw [this]
    exact hcK e₀ (hEK he₀) he₀C
  · have : (⟨d, hdY⟩ : ↥(centralizer ({x} : Set G))) = ⟨e₀, he₀C⟩ * ⟨x, hxC⟩ := Subtype.ext hd
    rw [this, map_mul]
    calc barMk ↥(centralizer ({x} : Set G)) ⟨e₀, he₀C⟩ * barMk ↥(centralizer ({x} : Set G)) ⟨x, hxC⟩ * l
        = barMk ↥(centralizer ({x} : Set G)) ⟨e₀, he₀C⟩ *
            (barMk ↥(centralizer ({x} : Set G)) ⟨x, hxC⟩ * l) := by rw [mul_assoc]
      _ = barMk ↥(centralizer ({x} : Set G)) ⟨e₀, he₀C⟩ *
            (l * barMk ↥(centralizer ({x} : Set G)) ⟨x, hxC⟩) := by rw [xbar_central hxC l]
      _ = (barMk ↥(centralizer ({x} : Set G)) ⟨e₀, he₀C⟩ * l) *
            barMk ↥(centralizer ({x} : Set G)) ⟨x, hxC⟩ := by rw [mul_assoc]
      _ = (l * barMk ↥(centralizer ({x} : Set G)) ⟨e₀, he₀C⟩) *
            barMk ↥(centralizer ({x} : Set G)) ⟨x, hxC⟩ := by
          rw [hcK e₀ (hEK he₀) he₀C]
      _ = l * (barMk ↥(centralizer ({x} : Set G)) ⟨e₀, he₀C⟩ *
            barMk ↥(centralizer ({x} : Set G)) ⟨x, hxC⟩) := by rw [mul_assoc]

theorem false_of_obs_x {x : G} {K A D J : Subgroup G} (hc : Ctx21 G x K A x D J)
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) : False := by
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := S3Rk1Basic.pcomp_of_circ hc.circ
  rcases FalseCtxS45Comp.pCompIn_eq_or_commute hc.obs.comp hK with hJK | hcomm
  · subst hJK
    exact false_of_obs_K hc h3
  · exact false_of_obs_ne hc h3 hcomm

end S3Prop29

theorem s3_a_ne_x {G : Type} [Group G] [Finite G] {x a : G} {K A D J : Subgroup G}
    (hc : Ctx21 G x K A a D J) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) : a ≠ x := fun hax =>
  S3Prop29.false_of_obs_x (hax ▸ hc) h3

end CFSG.GH74.Generic.BProg.B3
