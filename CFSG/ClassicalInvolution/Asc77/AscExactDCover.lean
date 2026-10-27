module

public import CFSG.ClassicalInvolution.Asc77.AscExactDTwin
public import CFSG.ClassicalInvolution.Asc77.AscExactDBasic

public section

open scoped commutatorElement MatrixGroups Pointwise

namespace CFSG.ClassicalInvolution.Asc77.ExactD

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

namespace TwinPair

variable (d : TwinPair p f Ω K K' z)
include d

theorem le_sup_of_centralizes {x y u : G} (hx : x ∈ K) (hy : y ∈ K') (hu : u = x * y)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hcent : oddProd K K' ≤ Subgroup.centralizer ({u} : Set G)) :
    K ≤ ((K ⊔ K') ⊓ Subgroup.centralizer (oddProd K K' : Set G)) ⊔ oddProd K K' := by
  classical
  set M : Subgroup G := K ⊔ K' with hM
  set N₀ : Subgroup G := oddProd K K' with hN₀
  set C : Subgroup G := M ⊓ Subgroup.centralizer (N₀ : Set G) with hC
  set H : Subgroup G := C ⊔ N₀ with hH
  have hMN₀ : M ≤ Subgroup.normalizer (N₀ : Set G) := d.sup_le_normalizer_oddProd
  have hMC : M ≤ Subgroup.normalizer (C : Set G) := le_normalizer_inf_centralizer hMN₀
  have hMH : M ≤ Subgroup.normalizer (H : Set G) := fun m hm =>
    Subgroup.inf_normalizer_le_normalizer_sup C N₀ ⟨hMC hm, hMN₀ hm⟩
  have hKM : K ≤ M := le_sup_left
  have hK'M : K' ≤ M := le_sup_right
  have huM : u ∈ M := hu ▸ M.mul_mem (hKM hx) (hK'M hy)
  have huC : u ∈ C :=
    ⟨huM, Subgroup.mem_centralizer_iff.mpr fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mp (hcent hn)⟩
  have huH : u ∈ H := (le_sup_left : C ≤ H) huC
  have hNK : oddCoreOf K ≤ H := (le_sup_left : oddCoreOf K ≤ N₀).trans le_sup_right
  have hKnH : K ≤ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp (hMH (hKM hk)) g)
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) g)
  obtain ⟨φ, hφs, hφk⟩ := d.hyp.exists_chart d.mem
  rcases d.K_le_or_chart_central hφs hφk (inf_le_right : H ⊓ K ≤ K) hKnH
      (le_inf hNK (oddCoreOf_le_self K)) with hKle | hcen
  · exact fun k hk => (hKle hk).1
  · exfalso
    have hcomm : ∀ k : G, k ∈ K → ⁅u, k⁆ ∈ H ⊓ K := by
      intro k hk
      refine ⟨?_, ?_⟩
      · have h1 : k * u⁻¹ * k⁻¹ ∈ H :=
          (Subgroup.mem_normalizer_iff.mp (hMH (hKM hk)) _).mp (H.inv_mem huH)
        have e : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
        rw [e]
        exact H.mul_mem huH h1
      · have h1 : u * k * u⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (d.sup_le_normalizer_left huM) k).mp hk
        have e : ⁅u, k⁆ = (u * k * u⁻¹) * k⁻¹ := by simp [commutatorElement_def]
        rw [e]
        exact K.mul_mem h1 (K.inv_mem hk)
    have hxc : ∀ (k : G) (hk : k ∈ K),
        ⁅φ ⟨x, hx⟩, φ ⟨k, hk⟩⁆ ∈ Subgroup.center SL(2, GaloisField p f) := by
      intro k hk
      have h1 := hcen _ (hcomm k hk)
      have hkyc : ⁅k, y⁆ ∈ oddCoreOf K ⊓ oddCoreOf K' :=
        d.comm_le (Subgroup.commutator_mem_commutator hk hy)
      have hw : ⁅y, k⁆ ∈ oddCoreOf K := by
        rw [← commutatorElement_inv k y]
        exact (oddCoreOf K).inv_mem hkyc.1
      have hn₁ : x * ⁅y, k⁆ * x⁻¹ ∈ oddCoreOf K := Balance.conj_mem_oddCoreIn hx hw
      have e : ⁅u, k⁆ = (x * ⁅y, k⁆ * x⁻¹) * ⁅x, k⁆ := by
        rw [hu]
        simp only [commutatorElement_def]
        group
      have hn₁K : x * ⁅y, k⁆ * x⁻¹ ∈ K := oddCoreOf_le_self K hn₁
      have hsub : (⟨⁅u, k⁆, (hcomm k hk).2⟩ : ↥K) =
          ⟨x * ⁅y, k⁆ * x⁻¹, hn₁K⟩ * ⁅(⟨x, hx⟩ : ↥K), ⟨k, hk⟩⁆ := Subtype.ext e
      have hker : φ ⟨x * ⁅y, k⁆ * x⁻¹, hn₁K⟩ = 1 :=
        (hφk _).mpr (mem_oddCoreOf_iff.mp hn₁).2
      rw [hsub, map_mul, hker, one_mul, map_commutatorElement] at h1
      exact h1
    have hxz : φ ⟨x, hx⟩ ∈ Subgroup.center SL(2, GaloisField p f) := by
      have : Group.IsPerfect SL(2, GaloisField p f) := ⟨d.isQuasisimple_sl2.1⟩
      refine mem_center_of_commutators_central fun s => ?_
      obtain ⟨k, rfl⟩ := hφs s
      exact hxc k k.2
    have hxN := d.mem_oddCore_or_mul_of_chart_central hφk hx hxz
    have huK' : u ∈ N₀ ⊔ K' := by
      rcases hxN with h | h
      · rw [hu]
        exact Subgroup.mul_mem_sup ((le_sup_left : oddCoreOf K ≤ N₀) h) hy
      · have e : u = (x * z) * (z⁻¹ * y) := by rw [hu]; group
        rw [e]
        exact Subgroup.mul_mem_sup ((le_sup_left : oddCoreOf K ≤ N₀) h)
          (K'.mul_mem (K'.inv_mem d.hz'.mem) hy)
    have huK'' : u ∈ K' := by
      refine mem_of_involution_mem_sup_odd (N := N₀) (fun g hg => hMN₀ (hK'M hg))
        (fun n hn => d.sup_le_normalizer_right (oddProd_le hn)) d.odd_oddProd
        (by rwa [sup_comm] at huK') hu2
    rcases d.hz'.unique u huK'' hu2 with h | h
    · exact hu1 h
    · exact huz h

theorem sup_le_centralizer_oddProd {u : G} (hu : u ∈ K ⊔ K') (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huz : u ≠ z) (hcent : oddProd K K' ≤ Subgroup.centralizer ({u} : Set G)) :
    K ⊔ K' ≤ Subgroup.centralizer (oddProd K K' : Set G) := by
  have hset : ((K ⊔ K' : Subgroup G) : Set G) = (K : Set G) * (K' : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K K' d.K_le
  have hu1' : u ∈ (K : Set G) * (K' : Set G) := hset ▸ hu
  obtain ⟨x, hx, y, hy, hxy⟩ := hu1'
  have hset' : ((K' ⊔ K : Subgroup G) : Set G) = (K' : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K' K d.K'_le
  have hu' : u ∈ K' ⊔ K := by rwa [sup_comm]
  have hu2' : u ∈ (K' : Set G) * (K : Set G) := hset' ▸ hu'
  obtain ⟨y', hy', x', hx', hxy'⟩ := hu2'
  have h1 := d.le_sup_of_centralizes hx hy hxy.symm hu2 hu1 huz hcent
  have h2 := d.symm.le_sup_of_centralizes hy' hx' hxy'.symm hu2 hu1 huz
    (by rwa [oddProd_comm])
  rw [oddProd_comm, sup_comm K' K] at h2
  exact le_centralizer_of_perfect_of_cover d.commutator_sup_eq oddProd_le
    d.sup_le_normalizer_oddProd d.odd_oddProd (sup_le h1 h2)

end TwinPair

end CFSG.ClassicalInvolution.Asc77.ExactD
