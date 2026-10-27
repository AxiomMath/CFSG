module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Tail1

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits.N

variable {G : Type} [Group G] [Finite G]
variable (d : Data G)

theorem Jg_le_of_normal {T : Subgroup G} (hT : (T.subgroupOf (Hg d)).Normal) (hX : Xg d ≤ T) :
    Jg d ≤ T := by
  have h1 : Subgroup.normalClosure (((Xg d).subgroupOf (Hg d) : Subgroup ↥(Hg d)) :
      Set ↥(Hg d)) ≤ T.subgroupOf (Hg d) :=
    Subgroup.normalClosure_le_normal fun x hx =>
      Subgroup.mem_subgroupOf.2 (hX (Subgroup.mem_subgroupOf.1 hx))
  intro j hj
  obtain ⟨j', hj', rfl⟩ := hj
  exact Subgroup.mem_subgroupOf.1 (h1 hj')

theorem centralizer_le_Kz (z₀ : G) (hZV : Zz d z₀ ≤ d.s56V) :
    centralizer (d.s56V : Set G) ≤ Kz d z₀ := by
  intro c hc
  have hcomm : ∀ v ∈ d.s56V, c * v * c⁻¹ = v := fun v hv => by
    have h := Subgroup.mem_centralizer_iff.1 hc v hv
    rw [← h]
    group
  refine ⟨Subgroup.centralizer_le_normalizer _ hc, mem_normalizer_iff.2 fun z => ⟨fun hz => ?_,
    fun hz => ?_⟩, fun y hy => ?_⟩
  · rw [hcomm z (hZV hz)]
    exact hz
  · have hu : c * z * c⁻¹ ∈ d.s56V := hZV hz
    have h2 := hcomm (c * z * c⁻¹) hu
    have : z = c * z * c⁻¹ := by
      calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
        _ = c⁻¹ * (c * (c * z * c⁻¹) * c⁻¹) * c := by rw [h2]
        _ = c * z * c⁻¹ := by group
    rw [this]
    exact hz
  · rw [hcomm y hy, mul_inv_cancel]
    exact one_mem _

theorem le_oddCoreSub_of_normal_odd {K : Subgroup (MulAut ↥d.s56V)} (hKH : K ≤ Hs d)
    (hKn : ∀ h ∈ Hs d, ∀ n ∈ K, h * n * h⁻¹ ∈ K) (hodd : Odd (Nat.card K)) :
    K ≤ oddCoreSub (Hs d) := by
  have hnorm : (K.subgroupOf (Hs d)).Normal :=
    ⟨fun n hn h => Subgroup.mem_subgroupOf.2 (hKn h h.2 n (Subgroup.mem_subgroupOf.1 hn))⟩
  have hodd' : Odd (Nat.card (K.subgroupOf (Hs d))) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
  have hle : K.subgroupOf (Hs d) ≤ standardComponentOddCore ↥(Hs d) := le_sSup ⟨hnorm, hodd'⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle (Subgroup.mem_subgroupOf.2 hk), rfl⟩

theorem centralizer_inf_Hs_conj_mem (hW : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d)
    {h c : MulAut ↥d.s56V} (hh : h ∈ Hs d)
    (hc : c ∈ centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) ⊓ Hs d) :
    h * c * h⁻¹ ∈ centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) ⊓ Hs d := by
  obtain ⟨hcC, hcH⟩ := Subgroup.mem_inf.1 hc
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun w hw => ?_,
    mul_mem (mul_mem hh hcH) (inv_mem hh)⟩
  have hw' : h⁻¹ * w * h⁻¹⁻¹ ∈ Ws d := hW _ (inv_mem hh) w hw
  have h1 := Subgroup.mem_centralizer_iff.1 hcC _ hw'
  calc w * (h * c * h⁻¹) = h * ((h⁻¹ * w * h⁻¹⁻¹) * c) * h⁻¹ := by group
    _ = h * (c * (h⁻¹ * w * h⁻¹⁻¹)) * h⁻¹ := by rw [h1]
    _ = h * c * h⁻¹ * w := by group

theorem commute_star_of_mem_Jp {N : Subgroup (MulAut ↥d.s56V)} (hNn : ∀ h ∈ Hs d, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hXN : ∀ x ∈ Xg d, ∀ n ∈ N, n * star d x = star d x * n) (hX : Xg d ≤ Hg d)
    {g : G} (hg : g ∈ Jp d) {n : MulAut ↥d.s56V} (hn : n ∈ N) : n * star d g = star d g * n := by
  let T : Subgroup G :=
    { carrier := {j | j ∈ Hg d ∧ ∀ n ∈ N, n * star d j = star d j * n}
      mul_mem' := by
        rintro j₁ j₂ ⟨h1, f1⟩ ⟨h2, f2⟩
        refine ⟨mul_mem h1 h2, fun n hn => ?_⟩
        show n * actFun d.s56V (j₁ * j₂) = actFun d.s56V (j₁ * j₂) * n
        rw [actFun_mul d.s56V h1 h2]
        calc n * (actFun d.s56V j₁ * actFun d.s56V j₂)
            = (n * star d j₁) * star d j₂ := by rw [mul_assoc]; rfl
          _ = (star d j₁ * n) * star d j₂ := by rw [f1 n hn]
          _ = star d j₁ * (n * star d j₂) := by rw [mul_assoc]
          _ = star d j₁ * (star d j₂ * n) := by rw [f2 n hn]
          _ = actFun d.s56V j₁ * actFun d.s56V j₂ * n := by rw [← mul_assoc]; rfl
      one_mem' := ⟨one_mem _, fun n _ => by
        show n * actFun d.s56V 1 = actFun d.s56V 1 * n
        rw [actFun_one]; simp⟩
      inv_mem' := by
        rintro j ⟨h1, f1⟩
        refine ⟨inv_mem h1, fun n hn => ?_⟩
        show n * actFun d.s56V j⁻¹ = actFun d.s56V j⁻¹ * n
        rw [actFun_inv d.s56V h1]
        have := f1 n hn
        have h2 : n * (star d j)⁻¹ = (star d j)⁻¹ * n := by
          calc n * (star d j)⁻¹ = (star d j)⁻¹ * (star d j * n) * (star d j)⁻¹ := by group
            _ = (star d j)⁻¹ * (n * star d j) * (star d j)⁻¹ := by rw [this]
            _ = (star d j)⁻¹ * n := by group
        exact h2 }
  have hTn : (T.subgroupOf (Hg d)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨hxH, hxf⟩ := (Subgroup.mem_subgroupOf.1 hx : (x : G) ∈ T)
    refine Subgroup.mem_subgroupOf.2 ⟨mul_mem (mul_mem g.2 hxH) (inv_mem g.2), fun n hn => ?_⟩
    have hgH : (g : G) ∈ Hg d := g.2
    have hĥ : star d (g : G) ∈ Hs d := actFun_mem_imgIn hgH hgH
    have hn' : (star d (g : G))⁻¹ * n * star d (g : G) ∈ N := by
      have := hNn _ (inv_mem hĥ) n hn
      simpa using this
    have h3 := hxf _ hn'
    show n * actFun d.s56V ((g : G) * x * (g : G)⁻¹) = actFun d.s56V ((g : G) * x * (g : G)⁻¹) * n
    rw [actFun_conj d.s56V hgH hxH]
    change n * (star d (g : G) * star d (x : G) * (star d (g : G))⁻¹) =
      star d (g : G) * star d (x : G) * (star d (g : G))⁻¹ * n
    calc n * (star d (g : G) * star d (x : G) * (star d (g : G))⁻¹)
        = star d (g : G) * (((star d (g : G))⁻¹ * n * star d (g : G)) * star d (x : G)) *
          (star d (g : G))⁻¹ := by group
      _ = star d (g : G) * (star d (x : G) * ((star d (g : G))⁻¹ * n * star d (g : G))) *
          (star d (g : G))⁻¹ := by rw [h3]
      _ = star d (g : G) * star d (x : G) * (star d (g : G))⁻¹ * n := by group
  have hXT : Xg d ≤ T := fun x hx => ⟨hX hx, hXN x hx⟩
  have hJT := Jg_le_of_normal d hTn hXT
  obtain ⟨-, j, hj, -, hjg⟩ := (mem_Jp_iff d).1 hg
  rw [← hjg]
  exact (hJT hj).2 n hn

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6
