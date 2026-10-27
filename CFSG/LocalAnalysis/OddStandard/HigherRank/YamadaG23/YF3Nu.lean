module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Abs

public section

open scoped IsMulCommutative

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {P X₀ Y N : Subgroup G}

private lemma norm_conj_eq {Q : Type*} [CommGroup Q] (σ τ : Q →* Q)
    (h3 : σ.comp (σ.comp σ) = MonoidHom.id Q)
    (h : σ.comp τ = τ.comp σ ∨ σ.comp τ = τ.comp (σ.comp σ)) :
    ((MonoidHom.id Q) * σ * σ.comp σ).comp τ =
      τ.comp ((MonoidHom.id Q) * σ * σ.comp σ) := by
  have h3' : ∀ x : Q, σ (σ (σ x)) = x := by
    intro x
    simpa [MonoidHom.comp_apply] using DFunLike.congr_fun h3 x
  rcases h with h | h
  · ext q
    have hq : σ (τ q) = τ (σ q) := DFunLike.congr_fun h q
    have hq2 : σ (σ (τ q)) = τ (σ (σ q)) := by
      rw [show σ (σ (τ q)) = σ (τ (σ q)) from congrArg σ hq,
        show σ (τ (σ q)) = τ (σ (σ q)) from DFunLike.congr_fun h (σ q)]
    change (τ q * σ (τ q)) * σ (σ (τ q)) = τ (q * σ q * σ (σ q))
    rw [hq2, hq]
    simp only [map_mul]
  · ext q
    have hq : σ (τ q) = τ (σ (σ q)) := DFunLike.congr_fun h q
    have hq2 : σ (σ (τ q)) = τ (σ q) := by
      rw [show σ (σ (τ q)) = σ (τ (σ (σ q))) from congrArg σ hq,
        show σ (τ (σ (σ q))) = τ (σ (σ (σ (σ q)))) from DFunLike.congr_fun h (σ (σ q)),
        h3' (σ q)]
    change (τ q * σ (τ q)) * σ (σ (τ q)) = τ (q * σ q * σ (σ q))
    rw [hq2, hq]
    simp only [map_mul]
    ac_rfl

theorem ext_nu (hC : ExtCtx P X₀ Y N) (hsq : ∀ y ∈ Y, y ^ 2 ∈ P) {k : G} (hkN : k ∈ N)
    (hk3 : k ^ 3 ∈ P) (hkn : ∀ n ∈ N, ∃ p ∈ P, n * k * n⁻¹ = k * p ∨ n * k * n⁻¹ = k⁻¹ * p)
    (hfix : ∀ y ∈ Y, y⁻¹ * (k * y * k⁻¹) ∈ X₀ → y ∈ X₀) :
    ∀ x ∈ X₀, x ∈ ⁅Y, N⁆ ⊔ P → x ∈ P := by
  have hPleY : P ≤ Y := hC.P_le.trans hC.X₀_le
  have hMnorm : (P.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff hPleY).mpr fun p y hp hy => hC.P_Y y hy p hp
  letI : (P.subgroupOf Y).Normal := hMnorm
  let Q := ↥Y ⧸ (P.subgroupOf Y)
  let mk : ↥Y →* Q := QuotientGroup.mk' (P.subgroupOf Y)
  haveI hQcomm : IsMulCommutative Q := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, _root_.commutator_def,
      Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_subgroupOf]
    change ⁅(a : G), (b : G)⁆ ∈ P
    exact ext_comm_mem hC hsq (a : G) a.2 (b : G) b.2
  have hkY : ∀ y ∈ Y, k * y * k⁻¹ ∈ Y := hC.Y_N k hkN
  let σY : ↥Y →* ↥Y :=
    { toFun := fun y => ⟨k * (y : G) * k⁻¹, hkY (y : G) y.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp only [Subgroup.coe_mul]; group }
  have hσM : P.subgroupOf Y ≤ (P.subgroupOf Y).comap σY := by
    intro p hp
    rw [Subgroup.mem_subgroupOf] at hp
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hC.P_N k hkN (p : G) hp
  let σ : Q →* Q := QuotientGroup.map (P.subgroupOf Y) (P.subgroupOf Y) σY hσM
  have hmkσ : ∀ y : ↥Y, σ (mk y) = mk (σY y) := fun _ => rfl
  have hconjP : ∀ p ∈ P, ∀ y ∈ Y, (p * y * p⁻¹)⁻¹ * y ∈ P := by
    intro p hp y hy
    have h1 : y⁻¹ * p⁻¹ * y ∈ P := by
      simpa using hC.P_Y y⁻¹ (Y.inv_mem hy) p⁻¹ (P.inv_mem hp)
    have h2 : p * (y⁻¹ * p⁻¹ * y) ∈ P := P.mul_mem hp h1
    have h3 : (p * y * p⁻¹)⁻¹ * y = p * (y⁻¹ * p⁻¹ * y) := by group
    rw [h3]
    exact h2
  have hmk_eq_iff : ∀ a b : ↥Y, mk a = mk b ↔ (a : G)⁻¹ * (b : G) ∈ P := by
    intro a b
    constructor
    · intro h
      have h1 : mk (a⁻¹ * b) = 1 := by
        rw [map_mul, map_inv, h, inv_mul_cancel]
      have h2 : (a⁻¹ * b) ∈ MonoidHom.ker (QuotientGroup.mk' (P.subgroupOf Y)) :=
        MonoidHom.mem_ker.mpr h1
      rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at h2
      simpa using h2
    · intro h
      have h2 : (a⁻¹ * b) ∈ MonoidHom.ker (QuotientGroup.mk' (P.subgroupOf Y)) := by
        rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
        exact h
      have h3 : (QuotientGroup.mk' (P.subgroupOf Y)) (a⁻¹ * b) = 1 :=
        MonoidHom.mem_ker.mp h2
      rw [map_mul, map_inv] at h3
      exact inv_mul_eq_one.mp h3
  have hexp : ∀ q : Q, q ^ 2 = 1 := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf Y) q
    have h : (w ^ 2) ∈ MonoidHom.ker (QuotientGroup.mk' (P.subgroupOf Y)) := by
      rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
      exact hsq (w : G) w.2
    have h2 : (QuotientGroup.mk' (P.subgroupOf Y)) (w ^ 2) = 1 := MonoidHom.mem_ker.mp h
    rwa [map_pow] at h2
  have hσ3comp : σ.comp (σ.comp σ) = MonoidHom.id Q := by
    apply QuotientGroup.monoidHom_ext
    ext y
    change σ (σ (σ (mk y))) = mk y
    rw [hmkσ, hmkσ, hmkσ, hmk_eq_iff]
    have h1 : (↑(σY (σY (σY y))) : G) = k ^ 3 * (y : G) * (k ^ 3)⁻¹ := by
      change k * (k * (k * (y : G) * k⁻¹) * k⁻¹) * k⁻¹ = k ^ 3 * (y : G) * (k ^ 3)⁻¹
      rw [pow_three']
      group
    rw [h1]
    exact hconjP (k ^ 3) hk3 (y : G) y.2
  let nu : G → G := fun y => y * (k * y * k⁻¹) * (k * (k * y * k⁻¹) * k⁻¹)
  have hnuY : ∀ y ∈ Y, nu y ∈ Y := by
    intro y hy
    exact Y.mul_mem (Y.mul_mem hy (hkY y hy)) (hkY _ (hkY y hy))
  let ν : Q →* Q := (MonoidHom.id Q) * σ * σ.comp σ
  have hνmk : ∀ y : ↥Y, ν (mk y) = mk ⟨nu (y : G), hnuY (y : G) y.2⟩ := by
    intro y
    have h1 : ν (mk y) = (mk y * σ (mk y)) * σ (σ (mk y)) := rfl
    rw [h1, hmkσ, hmkσ, ← map_mul, ← map_mul]
    congr 1
  have hσfix : ∀ q : Q, σ (ν q) = ν q := by
    have h3' : ∀ x : Q, σ (σ (σ x)) = x := by
      intro x
      simpa [MonoidHom.comp_apply] using DFunLike.congr_fun hσ3comp x
    intro q
    calc σ (ν q) = σ (q * σ q * σ (σ q)) := rfl
      _ = σ q * σ (σ q) * σ (σ (σ q)) := by rw [map_mul, map_mul]
      _ = σ q * σ (σ q) * q := by rw [h3']
      _ = q * σ q * σ (σ q) := by ac_rfl
      _ = ν q := rfl
  have hnuX0 : ∀ y ∈ Y, nu y ∈ X₀ := by
    intro y hy
    have h := hσfix (mk ⟨y, hy⟩)
    rw [hνmk, hmkσ] at h
    have hmem : ((k * nu y * k⁻¹)⁻¹ * nu y) ∈ P := (hmk_eq_iff _ _).mp h
    have hmem2 : (nu y)⁻¹ * (k * nu y * k⁻¹) ∈ P := by
      simpa only [mul_inv_rev, inv_inv] using P.inv_mem hmem
    exact hfix (nu y) (hnuY y hy) (hC.P_le hmem2)
  have hX0cong : ∀ a ∈ X₀, ∀ g ∈ N, (g * a * g⁻¹)⁻¹ * a ∈ P := by
    intro a ha g hg
    have hga : g * a * g⁻¹ ∈ X₀ := hC.X₀_N g hg a ha
    rcases hC.cosets a ha (g * a * g⁻¹) hga with haP | hgaP | h
    · exact P.mul_mem (P.inv_mem (hC.P_N g hg a haP)) haP
    · have haP' : a ∈ P := by
        have hconj : g⁻¹ * (g * a * g⁻¹) * g ∈ P := by
          simpa only [inv_inv] using hC.P_N g⁻¹ (N.inv_mem hg) (g * a * g⁻¹) hgaP
        have hcancel : g⁻¹ * (g * a * g⁻¹) * g = a := by group
        rwa [hcancel] at hconj
      exact P.mul_mem (P.inv_mem hgaP) haP'
    · have := P.inv_mem h
      simpa only [mul_inv_rev, inv_inv] using this
  let K' : Subgroup G := ((ν.comp mk).ker).map Y.subtype
  have hK'P : P ≤ K' := by
    intro p hp
    refine Subgroup.mem_map.mpr ⟨⟨p, hPleY hp⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    have hp1 : mk ⟨p, hPleY hp⟩ = 1 := by
      have hmem : (⟨p, hPleY hp⟩ : ↥Y) ∈
          MonoidHom.ker (QuotientGroup.mk' (P.subgroupOf Y)) := by
        rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
        exact hp
      exact MonoidHom.mem_ker.mp hmem
    show ν (mk ⟨p, hPleY hp⟩) = 1
    rw [hp1, map_one]
  have hcomm : ⁅Y, N⁆ ≤ K' := by
    rw [Subgroup.commutator_le]
    intro y hy n hn
    have hY : ⁅y, n⁆ ∈ Y := by
      have h1 : n * y * n⁻¹ ∈ Y := hC.Y_N n hn y hy
      have h2 : y * (n * y * n⁻¹)⁻¹ ∈ Y := Y.mul_mem hy (Y.inv_mem h1)
      simpa [commutatorElement_def, mul_inv_rev, mul_assoc] using h2
    let τY : ↥Y →* ↥Y :=
      { toFun := fun z => ⟨n * (z : G) * n⁻¹, hC.Y_N n hn (z : G) z.2⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp only [Subgroup.coe_mul]; group }
    have hτM : P.subgroupOf Y ≤ (P.subgroupOf Y).comap τY := by
      intro p hp
      rw [Subgroup.mem_subgroupOf] at hp
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact hC.P_N n hn (p : G) hp
    let τ : Q →* Q := QuotientGroup.map (P.subgroupOf Y) (P.subgroupOf Y) τY hτM
    have hτmk : ∀ z : ↥Y, τ (mk z) = mk (τY z) := fun _ => rfl
    have hdisj : σ.comp τ = τ.comp σ ∨ σ.comp τ = τ.comp (σ.comp σ) := by
      obtain ⟨p, hp, hk' | hk'⟩ := hkn n⁻¹ (N.inv_mem hn)
      · left
        apply QuotientGroup.monoidHom_ext
        ext z
        change mk (σY (τY z)) = mk (τY (σY z))
        rw [hmk_eq_iff]
        change (k * (n * (z : G) * n⁻¹) * k⁻¹)⁻¹
            * (n * (k * (z : G) * k⁻¹) * n⁻¹) ∈ P
        have hkn' : k * n = n * (k * p) := by rw [← hk']; group
        have hratio : (k * (n * (z : G) * n⁻¹) * k⁻¹)⁻¹
              * (n * (k * (z : G) * k⁻¹) * n⁻¹)
            = n * (k * ((p * (z : G) * p⁻¹)⁻¹ * (z : G)) * k⁻¹) * n⁻¹ := by
          rw [show k * (n * (z : G) * n⁻¹) * k⁻¹ = (k * n) * (z : G) * (k * n)⁻¹ by group,
            show n * (k * (z : G) * k⁻¹) * n⁻¹ = (n * k) * (z : G) * (n * k)⁻¹ by group,
            hkn']
          group
        rw [hratio]
        exact hC.P_N n hn _ (hC.P_N k hkN _ (hconjP p hp (z : G) z.2))
      · right
        apply QuotientGroup.monoidHom_ext
        ext z
        change mk (σY (τY z)) = mk (τY (σY (σY z)))
        rw [hmk_eq_iff]
        change (k * (n * (z : G) * n⁻¹) * k⁻¹)⁻¹
            * (n * (k * (k * (z : G) * k⁻¹) * k⁻¹) * n⁻¹) ∈ P
        have hkn' : k * n = n * (k⁻¹ * p) := by rw [← hk']; group
        have hratio : (k * (n * (z : G) * n⁻¹) * k⁻¹)⁻¹
              * (n * (k * (k * (z : G) * k⁻¹) * k⁻¹) * n⁻¹)
            = n * (k⁻¹ * (((p * (z : G) * p⁻¹)⁻¹ * (z : G))
                * ((z : G)⁻¹ * k ^ 3 * (z : G) * (k ^ 3)⁻¹)) * k) * n⁻¹ := by
          rw [show k * (n * (z : G) * n⁻¹) * k⁻¹ = (k * n) * (z : G) * (k * n)⁻¹ by group,
            show n * (k * (k * (z : G) * k⁻¹) * k⁻¹) * n⁻¹
              = (n * (k * k)) * (z : G) * (n * (k * k))⁻¹ by group,
            hkn']
          rw [pow_three']
          group
        rw [hratio]
        have huv : ((p * (z : G) * p⁻¹)⁻¹ * (z : G))
            * ((z : G)⁻¹ * k ^ 3 * (z : G) * (k ^ 3)⁻¹) ∈ P := by
          have hzv : (z : G)⁻¹ * k ^ 3 * (z : G) ∈ P := by
            simpa using hC.P_Y (z : G)⁻¹ (Y.inv_mem z.2) (k ^ 3) hk3
          exact P.mul_mem (hconjP p hp (z : G) z.2) (P.mul_mem hzv (P.inv_mem hk3))
        exact hC.P_N n hn _
          (by simpa only [inv_inv] using hC.P_N k⁻¹ (N.inv_mem hkN) _ huv)
    have hνconj : ν.comp τ = τ.comp ν := norm_conj_eq σ τ hσ3comp hdisj
    have hτfix : τ (ν (mk ⟨y, hy⟩)) = ν (mk ⟨y, hy⟩) := by
      rw [hνmk, hτmk, hmk_eq_iff]
      change (n * nu y * n⁻¹)⁻¹ * nu y ∈ P
      exact hX0cong (nu y) (hnuX0 y hy) n hn
    have hπ : mk ⟨⁅y, n⁆, hY⟩ = mk ⟨y, hy⟩ * (τ (mk ⟨y, hy⟩))⁻¹ := by
      rw [hτmk, ← map_inv, ← map_mul]
      congr 1
      ext
      change y * n * y⁻¹ * n⁻¹ = (y : G) * (n * (y : G) * n⁻¹)⁻¹
      group
    have hzero : ν (mk ⟨⁅y, n⁆, hY⟩) = 1 := by
      rw [hπ, map_mul, map_inv]
      have h1 : ν (τ (mk ⟨y, hy⟩)) = τ (ν (mk ⟨y, hy⟩)) :=
        DFunLike.congr_fun hνconj (mk ⟨y, hy⟩)
      rw [h1, hτfix]
      simp
    exact Subgroup.mem_map.mpr
      ⟨⟨⁅y, n⁆, hY⟩, by rw [MonoidHom.mem_ker]; exact hzero, rfl⟩
  have hsup_le : ⁅Y, N⁆ ⊔ P ≤ K' := sup_le hcomm hK'P
  intro x hxX0 hxsup
  have hxY : x ∈ Y := hC.X₀_le hxX0
  have hxK : x ∈ K' := hsup_le hxsup
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxK
  have hzx' : z = ⟨x, hxY⟩ := Subtype.ext hzx
  have hker : ν (mk ⟨x, hxY⟩) = 1 := by
    rw [← hzx']
    exact MonoidHom.mem_ker.mp hz
  have hexpq : (mk ⟨x, hxY⟩) ^ 2 = 1 := hexp _
  have hσx : σ (mk ⟨x, hxY⟩) = mk ⟨x, hxY⟩ := by
    rw [hmkσ, hmk_eq_iff]
    change (k * x * k⁻¹)⁻¹ * x ∈ P
    exact hX0cong x hxX0 k hkN
  have hσ2x : σ (σ (mk ⟨x, hxY⟩)) = mk ⟨x, hxY⟩ := by rw [hσx, hσx]
  have hfixnu : ν (mk ⟨x, hxY⟩) = mk ⟨x, hxY⟩ := by
    change (mk ⟨x, hxY⟩ * σ (mk ⟨x, hxY⟩)) * σ (σ (mk ⟨x, hxY⟩)) = mk ⟨x, hxY⟩
    rw [hσx, hσx, mul_assoc, ← pow_two, hexpq, mul_one]
  rw [hfixnu] at hker
  have hmem : (⟨x, hxY⟩ : ↥Y) ∈ MonoidHom.ker (QuotientGroup.mk' (P.subgroupOf Y)) :=
    MonoidHom.mem_ker.mpr hker
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hmem
  exact hmem

end CFSG.OddStandard.HigherRank.YamadaG23
