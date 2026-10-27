module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Data11J
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Step3b
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Transport
public import Certificates.Certificate25131

public section

namespace CFSG.EvenSporadicStandard.J4Std.Data11

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

variable {G : Type} [Group G] (ι : J →* G) (hι : Function.Injective ι)

theorem mem_map_Eg (hM : MatFacts) {u : G}
    (hu : u ∈ (Eg uJ 11).map ι) : ∃ c < 2 ^ 11, u = ι (eta uJ 11 c) := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hu
  obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hx
  exact ⟨c, hc, rfl⟩

variable (hM : MatFacts)
  (hm : MaskData)
include hι hM hm

theorem fix_G : ∀ u ∈ (Eg uJ 11).map ι, ι pJ * u = u * ι pJ → u = 1 ∨ u = ι u0J := by
  intro u hu hc
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hu
  have hc' : pJ * x = x * pJ := hι (by simpa only [map_mul] using hc)
  rcases fix_J hM hm hx hc' with rfl | rfl
  · exact Or.inl (map_one ι)
  · exact Or.inr rfl

theorem comm_G : ∀ s : G, (∀ u ∈ (Eg uJ 11).map ι, s * u * s⁻¹ ∈ (Eg uJ 11).map ι) →
    s * ι pJ = ι pJ * s →
    (∃ k : ℕ, ∀ u ∈ (Eg uJ 11).map ι, s * (s * u * s⁻¹) * s⁻¹ = ι pJ ^ k * u * (ι pJ ^ k)⁻¹) →
    ∃ m : ℕ, ∀ u ∈ (Eg uJ 11).map ι, s * u * s⁻¹ = ι pJ ^ m * u * (ι pJ ^ m)⁻¹ := by
  intro s hs hsp ⟨k, hk⟩
  have hsetup := (maskSetup_J hM hm).map ι hι
  have h1 : ι (eta uJ 11 1) ∈ (Eg uJ 11).map ι :=
    Subgroup.mem_map_of_mem ι (eta_mem_Eg 11 le_rfl 1)
  obtain ⟨y, hy_lt, hy⟩ := mem_map_Eg ι hM (hs _ h1)
  obtain ⟨m, -, hmy⟩ := conj_comm_pow hsetup hm hsp hy hy_lt (hk _ h1)
  refine ⟨m, fun u hu => ?_⟩
  obtain ⟨c, hc, rfl⟩ := mem_map_Eg ι hM hu
  exact conj_eq_of_pPow hsetup hm hsp hmy hc

omit hM in
theorem cent_G :
    ∀ h ∈ Hloc ι.range ((Eg uJ 11).map ι), ι pJ * h = h * ι pJ →
      ∃ k : ℕ, ∃ u ∈ (Eg uJ 11).map ι, h = ι pJ ^ k * u := by
  intro h hh hc
  obtain ⟨j, hj, rfl⟩ := (mem_Hloc_map ι hι (Eg uJ 11)).1 hh
  have hc' : pJ * j = j * pJ := hι (by simpa only [map_mul] using hc)
  obtain ⟨k, e, he, hje⟩ := cent_J hm (mem_Hloc_top_iff.1 hj) hc'
  exact ⟨k, ι e, Subgroup.mem_map_of_mem ι he, by rw [hje, map_mul, map_pow]⟩

end CFSG.EvenSporadicStandard.J4Std.Data11

namespace CFSG.EvenSporadicStandard.J4Std

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.EvenSporadicStandard.J4Std.Data11

theorem localData11_J4
    {G : Type} [Group G] (ι : J →* G)
    (hι : Function.Injective ι) :
    ∃ p q u0 : G, LocalData11 ι.range ((Eg uJ 11).map ι) p q u0 := by
  have hM := j4Facts.mat
  have hm := maskData_of_chk Certificates.certificate25131
  refine ⟨ι pJ, ι qJ, ι u0J, ?_⟩
  have hp1 : ι pJ ≠ 1 := fun h => pJ_ne_one hM hm (hι (by rw [h, map_one]))
  have hp11 : ι pJ ^ 11 = 1 := by rw [← map_pow, pJ_pow hM, map_one]
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact
  { p_mem := (mem_Hloc_map ι hι _).2 ⟨pJ, mem_Hloc_top_iff.2 pJ_mem, rfl⟩
    q_mem := (mem_Hloc_map ι hι _).2 ⟨qJ, mem_Hloc_top_iff.2 qJ_mem, rfl⟩
    u0_mem := Subgroup.mem_map_of_mem ι u0J_mem
    u0_ne := fun h => u0J_ne hM (hι (by rw [h, map_one]))
    p_order := orderOf_eq_prime hp11 hp1
    q_conj := by
      rw [mul_inv_eq_iff_eq_mul]
      simpa only [map_mul, map_pow] using congrArg ι (qJ_mul_pJ hM)
    u0_fix := by simpa only [map_mul] using congrArg ι (pJ_comm_u0J hM hm)
    fix := fix_G ι hι hM hm
    cent := cent_G ι hι hm
    comm := comm_G ι hι hM hm }

end CFSG.EvenSporadicStandard.J4Std
