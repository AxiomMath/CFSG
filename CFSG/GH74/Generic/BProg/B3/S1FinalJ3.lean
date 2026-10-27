module

public import CFSG.GH74.Generic.BProg.B3.S1FinalJ2
public import CFSG.GH74.Generic.BProg.B3.LocBalL3

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1FinalJ3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.GH74.L5U5 Subgroup
open CFSG.GH74.Generic.BProg.B3.S1FinalDefs CFSG.GH74.Generic.BProg.B3.S1FinalJ1
  CFSG.GH74.Generic.BProg.B3.S1FinalJ2
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J J₁ J₂ : Subgroup G}

theorem conj_injective (H : JSetup x K A a D J J₁ J₂) :
    Function.Injective (MulAut.conj : J0 a J →* MulAut (J0 a J)) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  apply H.center_J0
  intro g
  have h := congrArg (fun σ : MulAut (J0 a J) => σ g) hz
  have h' : z * g * z⁻¹ = g := h
  exact (mul_inv_eq_iff_eq_mul.1 h').symm

theorem aut_mul_conj_mul_inv {L : Type} [Group L] (γ : MulAut L) (g : L) :
    γ * MulAut.conj g * γ⁻¹ = MulAut.conj (γ g) := by
  ext y
  simp [MulAut.conj_apply]

theorem A_le_NJ (H : JSetup x K A a D J J₁ J₂) : A ≤ NJ a J := fun e he =>
  ⟨H.hAJ he, Subgroup.mem_centralizer_singleton_iff.2 (H.hAcomm e he a H.haA)⟩

@[expose] noncomputable def rhoA (H : JSetup x K A a D J J₁ J₂) : ↥A →* MulAut (J0 a J) :=
  (rho H.hJa).comp (Subgroup.inclusion (A_le_NJ H))

theorem rhoA_sq (H : JSetup x K A a D J J₁ J₂) (e : ↥A) : rhoA H e * rhoA H e = 1 := by
  rw [← map_mul]
  have : e * e = 1 := Subtype.ext (H.hAsq e e.2)
  rw [this, map_one]

theorem mem_image_rho (H : JSetup x K A a D J J₁ J₂) {X : Subgroup G} (hXA : X ≤ A)
    {r : MulAut (J0 a J)}
    (hr : r ∈ ((PumpCalc.bar a X).subgroupOf (normalizer ((PumpCalc.bar a J :
      Subgroup (barQ ↥(centralizer ({a} : Set G)))) : Set (barQ ↥(centralizer ({a} : Set G)))))).map
        (rhoL (PumpCalc.bar a J))) :
    ∃ e : ↥A, (e : G) ∈ X ∧ r = rhoA H e := by
  obtain ⟨m, hm, rfl⟩ := hr
  obtain ⟨g, hg, hgm⟩ := Subgroup.mem_subgroupOf.1 hm
  have hgX : (g : G) ∈ X := Subgroup.mem_subgroupOf.1 hg
  refine ⟨⟨(g : G), hXA hgX⟩, hgX, ?_⟩
  show rhoL (PumpCalc.bar a J) m = rhoL (PumpCalc.bar a J) (toBarNorm H.hJa ⟨(g : G), A_le_NJ H (hXA hgX)⟩)
  congr 1
  exact Subtype.ext hgm.symm

theorem locBal32_of_inner (H : JSetup x K A a D J J₁ J₂) (hL : B1.QShape3SD (J0 a J))
    {X : Subgroup G} (hXA : X ≤ A)
    (hin : ∀ e : ↥A, rhoA H e ∈ (MulAut.conj : J0 a J →* MulAut (J0 a J)).range) :
    IsLocBal32 (J0 a J) (((PumpCalc.bar a X).subgroupOf (normalizer ((PumpCalc.bar a J :
      Subgroup (barQ ↥(centralizer ({a} : Set G)))) : Set (barQ ↥(centralizer ({a} : Set G)))))).map
        (rhoL (PumpCalc.bar a J))) := by
  classical
  set R := ((PumpCalc.bar a X).subgroupOf (normalizer ((PumpCalc.bar a J :
      Subgroup (barQ ↥(centralizer ({a} : Set G)))) : Set (barQ ↥(centralizer ({a} : Set G)))))).map
        (rhoL (PumpCalc.bar a J)) with hR
  have hRInn : R ≤ (MulAut.conj : J0 a J →* MulAut (J0 a J)).range := fun r hr => by
    obtain ⟨e, -, rfl⟩ := mem_image_rho H hXA hr
    exact hin e
  set B' : Subgroup (J0 a J) := R.comap (MulAut.conj : J0 a J →* MulAut (J0 a J)) with hB'
  have hB'map : B'.map (MulAut.conj : J0 a J →* MulAut (J0 a J)) = R := by
    rw [hB', Subgroup.map_comap_eq, inf_eq_right.2 hRInn]
  have hB'sq : ∀ b ∈ B', b * b = 1 := by
    intro b hb
    obtain ⟨e, -, he⟩ := mem_image_rho H hXA (Subgroup.mem_comap.1 hb)
    apply conj_injective H
    rw [map_mul, he, rhoA_sq H e, map_one]
  have := locBal32_L3_inner hL B' hB'sq
  rwa [hB'map] at this

theorem false_of_inner (H : JSetup x K A a D J J₁ J₂) (hL : B1.QShape3SD (J0 a J))
    (hin : ∀ e : ↥A, rhoA H e ∈ (MulAut.conj : J0 a J →* MulAut (J0 a J)).range) : False := by
  rcases H.hc.obs_cases with h2 | ⟨h1, -⟩ | ⟨-, e', he'A, he'N, -⟩
  · exact Obs32.not_locBal32_rank2 H.hc.obs h2 (locBal32_of_inner H hL H.hc.obs.D_le.1 hin)
  · exact Obs32.not_locBal32_rank1 H.hc.obs h1 H.hAJ (locBal32_of_inner H hL le_rfl hin)
  · exact he'N (H.hAJ he'A)

section Outer

variable (H : JSetup x K A a D J J₁ J₂)

include H

theorem hAcard : Nat.card ↥A = 8 := H.hc.src.2.2.1

theorem hxaA : x * a ∈ A := A.mul_mem H.hxA H.haA

theorem rho_a : rhoA H ⟨a, H.haA⟩ = 1 :=
  (rho_eq_one_iff H.hc.obs.comp ⟨a, A_le_NJ H H.haA⟩).2 H.haS

theorem rho_xa : rhoA H ⟨x * a, hxaA H⟩ = MulAut.conj (beta0 H) :=
  rho_of_mem H.hJa ⟨x * a, A_le_NJ H (hxaA H)⟩ (H.hJ₂ H.hb)

theorem rho_x : rhoA H ⟨x, H.hxA⟩ = MulAut.conj (beta0 H) := by
  have h : (⟨x, H.hxA⟩ : ↥A) = ⟨x * a, hxaA H⟩ * ⟨a, H.haA⟩ := by
    apply Subtype.ext
    show x = x * a * a
    rw [mul_assoc, H.hAsq a H.haA, mul_one]
  rw [h, map_mul, rho_a H, rho_xa H, mul_one]

@[expose] noncomputable def Tin : Subgroup G :=
  ((MulAut.conj : J0 a J →* MulAut (J0 a J)).range.comap (rhoA H)).map A.subtype

theorem mem_Tin {e : G} : e ∈ Tin H ↔ ∃ he : e ∈ A,
    rhoA H ⟨e, he⟩ ∈ (MulAut.conj : J0 a J →* MulAut (J0 a J)).range := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, hg⟩
  · rintro ⟨he, hin⟩
    exact ⟨⟨e, he⟩, hin, rfl⟩

theorem Tin_le : Tin H ≤ A := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem a_mem_Tin : a ∈ Tin H := (mem_Tin H).2 ⟨H.haA, by rw [rho_a H]; exact one_mem _⟩

theorem x_mem_Tin : x ∈ Tin H := (mem_Tin H).2 ⟨H.hxA, by rw [rho_x H]; exact ⟨beta0 H, rfl⟩⟩

theorem A2_le_Tin : closure ({a, x} : Set G) ≤ Tin H := by
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | hg
  · exact a_mem_Tin H
  · rw [Set.mem_singleton_iff.1 hg]; exact x_mem_Tin H

theorem four_le_card_A2 : 4 ≤ Nat.card ↥(closure ({a, x} : Set G)) := by
  have hlt : zpowers a < closure ({a, x} : Set G) := by
    refine lt_of_le_of_ne ((Subgroup.zpowers_le).2 (Subgroup.subset_closure (Set.mem_insert _ _))) ?_
    intro heq
    have hxz : x ∈ zpowers a := heq ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    rcases B1.PilotS5.mem_zpowers_of_two H.ha2 hxz with h1 | h1
    · have := H.hx2
      rw [h1, orderOf_one] at this
      omega
    · exact H.hax h1.symm
  have h2 := Obs.two_mul_card_le_of_lt hlt
  rw [Nat.card_zpowers, H.ha2] at h2
  omega

theorem orderOf_conj_beta0 : orderOf (MulAut.conj (beta0 H) : MulAut (J0 a J)) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, pow_two, beta0_mul_self H, map_one]
  · intro h
    exact beta0_ne_one H (conj_injective H (by rw [h, map_one]))

theorem rho_values_A2 : ∀ (e : G) (he : e ∈ A), e ∈ closure ({a, x} : Set G) →
    rhoA H ⟨e, he⟩ = 1 ∨ rhoA H ⟨e, he⟩ = MulAut.conj (beta0 H) := by
  set Pm : Subgroup G := ((zpowers (MulAut.conj (beta0 H) : MulAut (J0 a J))).comap
    (rhoA H)).map A.subtype with hPm
  have hle : closure ({a, x} : Set G) ≤ Pm := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact ⟨⟨g, H.haA⟩, by
        show rhoA H ⟨g, H.haA⟩ ∈ zpowers _
        rw [rho_a H]; exact one_mem _, rfl⟩
    · rw [Set.mem_singleton_iff.1 hg]
      exact ⟨⟨x, H.hxA⟩, by
        show rhoA H ⟨x, H.hxA⟩ ∈ zpowers _
        rw [rho_x H]; exact Subgroup.mem_zpowers _, rfl⟩
  intro e he hcl
  obtain ⟨g, hg, hge⟩ := hle hcl
  have hg' : g = ⟨e, he⟩ := Subtype.ext hge
  rw [hg'] at hg
  exact B1.PilotS5.mem_zpowers_of_two (orderOf_conj_beta0 H) hg

theorem Tin_eq_A2 {c : G} (hcA : c ∈ A) (hcout : rhoA H ⟨c, hcA⟩ ∉
    (MulAut.conj : J0 a J →* MulAut (J0 a J)).range) : Tin H = closure ({a, x} : Set G) := by
  have hlt : Tin H < A := by
    refine lt_of_le_of_ne (Tin_le H) (fun h => hcout ?_)
    have hc : c ∈ Tin H := by rw [h]; exact hcA
    exact ((mem_Tin H).1 hc).choose_spec
  have h2 := Obs.two_mul_card_le_of_lt hlt
  rw [hAcard H] at h2
  have h4 := four_le_card_A2 H
  exact (Subgroup.eq_of_le_of_card_ge (A2_le_Tin H) (by omega)).symm

theorem c_not_mem_A2 {c : G} (hcA : c ∈ A) (hcout : rhoA H ⟨c, hcA⟩ ∉
    (MulAut.conj : J0 a J →* MulAut (J0 a J)).range) : c ∉ closure ({a, x} : Set G) := fun h => by
  rw [← Tin_eq_A2 H hcA hcout] at h
  exact hcout ((mem_Tin H).1 h).choose_spec

theorem A_eq_closure {c : G} (hcA : c ∈ A) (hcout : rhoA H ⟨c, hcA⟩ ∉
    (MulAut.conj : J0 a J →* MulAut (J0 a J)).range) : A = closure ({a, x, c} : Set G) := by
  have hle : closure ({a, x, c} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact H.haA
    · rcases hg with rfl | hg
      · exact H.hxA
      · rw [Set.mem_singleton_iff.1 hg]; exact hcA
  have hlt : closure ({a, x} : Set G) < closure ({a, x, c} : Set G) := by
    refine lt_of_le_of_ne (Subgroup.closure_mono (fun g hg => ?_)) (fun h => ?_)
    · rcases hg with rfl | hg
      · exact Set.mem_insert _ _
      · rw [Set.mem_singleton_iff.1 hg]
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact c_not_mem_A2 H hcA hcout (h ▸ Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))
  have h2 := Obs.two_mul_card_le_of_lt hlt
  have h4 := four_le_card_A2 H
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hAcard H]; omega)).symm

theorem inner_values {c : G} (hcA : c ∈ A) (hcout : rhoA H ⟨c, hcA⟩ ∉
    (MulAut.conj : J0 a J →* MulAut (J0 a J)).range) (e : G) (he : e ∈ A)
    (hin : rhoA H ⟨e, he⟩ ∈ (MulAut.conj : J0 a J →* MulAut (J0 a J)).range) :
    rhoA H ⟨e, he⟩ = 1 ∨ rhoA H ⟨e, he⟩ = MulAut.conj (beta0 H) := by
  have : e ∈ Tin H := (mem_Tin H).2 ⟨he, hin⟩
  rw [Tin_eq_A2 H hcA hcout] at this
  exact rho_values_A2 H e he this

end Outer

end S1FinalJ3

end CFSG.GH74.Generic.BProg.B3
