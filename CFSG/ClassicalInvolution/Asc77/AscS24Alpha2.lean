module

public import CFSG.ClassicalInvolution.Asc77.AscS24Alpha
public import CFSG.ClassicalInvolution.Asc77.AscE18FromNT
public import CFSG.ClassicalInvolution.Asc77.AscT7BLocal23
public import CFSG.ClassicalInvolution.Asc77.AscT7ED2
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian)

set_option linter.unusedSectionVars false


section TwoThree

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem sup_centralizer_eq_top_of [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) :
    Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤ := by
  have hE : ThmEWithSylow p f := thmEWithSylow_of_nonToral f G2D4Models.g2NonToralGenerate_all
  have htr : C23_2_trans p f := c23_2_trans_proved p f
  obtain ⟨huK, huW, hu2, hu1, huz⟩ := hd.hu
  have hstd : StdCent Ω K
      (Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G)) z :=
    hs.stdCent_of_twin le_sup_right fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
      obtain ⟨c, hcz, hcu⟩ := c23_2_fuse G Ω K K' z hs W hd.hW hd.hzW u huK huW hu1
        huz hu2 L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
      intro a ha
      have ha' : a * (x * y) = (x * y) * a := Subgroup.mem_centralizer_singleton_iff.mp ha
      have hu' : u = c⁻¹ * (x * y) * c := by rw [← hcu]; group
      have hcomm : (c⁻¹ * a * c) * u = u * (c⁻¹ * a * c) := by
        have e1 : c⁻¹ * (a * (x * y)) * c = c⁻¹ * ((x * y) * a) * c := by rw [ha']
        calc (c⁻¹ * a * c) * u = c⁻¹ * (a * (x * y)) * c := by rw [hu']; group
          _ = c⁻¹ * ((x * y) * a) * c := e1
          _ = u * (c⁻¹ * a * c) := by rw [hu']; group
      have hcH : c ∈ Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_sup_right hcz
      have ha'H : c⁻¹ * a * c ∈
          Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
      have : a = c * (c⁻¹ * a * c) * c⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcH ha'H) (Subgroup.inv_mem _ hcH)
  exact thmE_apply hE hs.stand hs.hz hs.hK' hs.hne hstd
    (htr G Ω K K' z hs W hd.hW hd.hzW u huK huW hu1 huz hu2)

end TwoThree

namespace Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u g : G}
  (C : Ctx p f Ω K K' W S R R' z u g)

include C

theorem isElemAbelian2_conjSub {A : Subgroup G} (hA : IsElemAbelian2 A 2) (n : G) :
    IsElemAbelian2 (conjSub n A) 2 := by
  refine ⟨?_, fun x hx => ?_⟩
  · have hinj : Function.Injective (MulAut.conj n).toMonoidHom := (MulAut.conj n).injective
    rw [show conjSub n A = A.map (MulAut.conj n).toMonoidHom from rfl,
      Subgroup.card_map_of_injective hinj]
    exact hA.1
  · rw [mem_conjSub_iff] at hx
    have h := hA.2 _ hx
    calc x * x = n * ((n⁻¹ * x * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
      _ = 1 := by rw [h]; group

theorem normalizer_alpha {α₀ : Subgroup G}
    (halpha : ∀ A : Subgroup G, A ≤ C.B → IsElemAbelian2 A 2 → alphaOf A = α₀)
    {A₀ : Subgroup G} (hA₀B : A₀ ≤ C.B) (hA₀ : IsElemAbelian2 A₀ 2) {n : G}
    (hn : n ∈ Subgroup.normalizer (C.B : Set G)) : n ∈ Subgroup.normalizer (α₀ : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  have hAB : conjSub n A₀ ≤ C.B := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * x * n)).mp (hA₀B hx)
    have : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
    rwa [this] at h1
  have h1 := halpha _ hAB (C.isElemAbelian2_conjSub hA₀ n)
  rw [alphaOf_conjSub, halpha A₀ hA₀B hA₀] at h1
  exact h1

theorem alphaOf_eq_bot [IsSimpleGroup G]
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥)
    (hL : if piSign p f then LayerLieType p f Ω C.e0 .PSL 3
      else LayerLieType p f Ω C.e0 .PSU 3) :
    ∀ A : Subgroup G, A ≤ C.B → IsElemAbelian2 A 2 → alphaOf A = ⊥ := by
  have hD : IsElemAbelian2 (Subgroup.closure ({u, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair C.u_sq C.z_sq C.u_ne_one C.hs.hz.ne_one C.u_ne_z C.comm_uz
  have hDB : Subgroup.closure ({u, z} : Set G) ≤ C.B := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact C.u_mem_B
    · exact C.z_mem_B
  obtain ⟨hodd, halpha⟩ := lemma54_odd_and_eq (C.hyp51_B hZ hL) hDB hD
  have hCz : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    (C.centralizer_z_le_gamma2 hZ).trans (gamma2_le_normalizer_alphaOf halpha _)
  obtain ⟨g₀, hg₀, hg₀u⟩ := T7C2.exists_g0 C.hs C.hd
  have hg₀α := C.normalizer_alpha halpha hDB hD (C.mem_normalizer_B hZ hg₀)
  have hCu : Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
    intro c hc
    have hc' : g₀ * c * g₀⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      have hz : z = g₀ * u * g₀⁻¹ := by rw [← hg₀u]; group
      rw [hz]
      calc g₀ * c * g₀⁻¹ * (g₀ * u * g₀⁻¹) = g₀ * (c * u) * g₀⁻¹ := by group
        _ = g₀ * (u * c) * g₀⁻¹ := by rw [hcu]
        _ = g₀ * u * g₀⁻¹ * (g₀ * c * g₀⁻¹) := by group
    have h1 := hCz hc'
    have : c = g₀⁻¹ * (g₀ * c * g₀⁻¹) * g₀ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₀α) h1) hg₀α
  have hN : Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← sup_centralizer_eq_top_of C.hs C.hd]
    exact sup_le hCu hCz
  have hα := T7B.eq_bot_of_normalizer_eq_top hodd hN (T7B.two_dvd_natCard C.hs.hz)
  intro A hAB hA
  rw [halpha A hAB hA, hα]

end Ctx

end CFSG.ClassicalInvolution.Asc77.S24
