module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2

open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

structure OmegaData (f p : ℕ) (Fs N Ω : Subgroup K) : Prop where
  le : Ω ≤ Fs
  exp : ∀ x ∈ Ω, x ^ f = 1
  central : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ w ∈ Ω, w * ⁅x, y⁆ = ⁅x, y⁆ * w
  norm : N ≤ normalizer (Ω : Set K)
  faithful : ∀ t ∈ N, ∀ n : ℕ, t ^ (p ^ n) = 1 →
    (∀ x ∈ Ω, x⁻¹ * (t * x * t⁻¹) ∈ ⁅Ω, Ω⁆) → ∀ x ∈ Fs, t * x = x * t

theorem commutator_le_self (H : Subgroup K) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem normalizer_le_normalizer_commutator (H : Subgroup K) :
    normalizer (H : Set K) ≤ normalizer ((⁅H, H⁆ : Subgroup K) : Set K) := by
  have key : ∀ g ∈ normalizer (H : Set K), ∀ y ∈ (⁅H, H⁆ : Subgroup K), g * y * g⁻¹ ∈ ⁅H, H⁆ := by
    intro g hg y hy
    have hle : ⁅H, H⁆ ≤ (⁅H, H⁆ : Subgroup K).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      show (MulAut.conj g).toMonoidHom ⁅a, b⁆ ∈ ⁅H, H⁆
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator ((mem_normalizer_iff.mp hg a).mp ha)
        ((mem_normalizer_iff.mp hg b).mp hb)
    exact hle hy
  intro g hg
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have h2 := key g⁻¹ ((normalizer (H : Set K)).inv_mem hg) _ hy
  simpa [mul_assoc] using h2

theorem exists_omega {f p : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) (hp : p.Prime) (hpf : p ≠ f)
    {Fs N : Subgroup K} (hFs : IsPGroup f Fs) (hN : N ≤ normalizer (Fs : Set K)) :
    ∃ Ω : Subgroup K, OmegaData f p Fs N Ω := by
  have hf : f.Prime := Fact.out
  obtain ⟨C₀, hC₀⟩ := (CFSG.SectionRank.Ccomm.thompson_critical_subgroup (P := ↥Fs) (p := f) hFs).1
  have hC₀p : IsPGroup f ↥C₀ := hFs.to_subgroup C₀
  haveI : Fact (IsPGroup f ↥C₀) := ⟨hC₀p⟩
  have hC₀full := hC₀
  obtain ⟨hchar, hfrat, -, -⟩ := hC₀
  set Cₐ : Subgroup K := C₀.map Fs.subtype with hCₐ
  have hCₐle : Cₐ ≤ Fs := Subgroup.map_subtype_le C₀
  have hCₐp : IsPGroup f Cₐ := hFs.to_le hCₐle
  have hcl₀ : ∀ a ∈ C₀, ∀ b ∈ C₀, ∀ w ∈ C₀, w * ⁅a, b⁆ = ⁅a, b⁆ * w := by
    intro a ha b hb w hw
    have h1 : ⁅(⟨a, ha⟩ : ↥C₀), ⟨b, hb⟩⁆ ∈ frattini ↥C₀ :=
      CFSG.commutator_le_frattini_of_isPGroup (R := ↥C₀) (p := f)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have h2 : (C₀.subtype ⁅(⟨a, ha⟩ : ↥C₀), ⟨b, hb⟩⁆ : ↥Fs) ∈ centralizer (C₀ : Set ↥Fs) :=
      (hfrat ⟨_, h1, rfl⟩).2
    rw [mem_centralizer_iff] at h2
    exact h2 w hw
  have hpow₀ : ∀ a ∈ C₀, ∀ w ∈ C₀, w * a ^ f = a ^ f * w := by
    intro a ha w hw
    have h1 : (⟨a, ha⟩ : ↥C₀) ^ f ∈ frattini ↥C₀ :=
      CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥C₀) (p := f) _
    have h2 : (C₀.subtype ((⟨a, ha⟩ : ↥C₀) ^ f) : ↥Fs) ∈ centralizer (C₀ : Set ↥Fs) :=
      (hfrat ⟨_, h1, rfl⟩).2
    rw [mem_centralizer_iff] at h2
    exact h2 w hw
  have hcl : ∀ x ∈ Cₐ, ∀ y ∈ Cₐ, ∀ w ∈ Cₐ, w * ⁅x, y⁆ = ⁅x, y⁆ * w := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨w, hw, rfl⟩
    exact congrArg Subtype.val (hcl₀ a ha b hb w hw)
  have hpow : ∀ x ∈ Cₐ, ∀ w ∈ Cₐ, w * x ^ f = x ^ f * w := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨w, hw, rfl⟩
    exact congrArg Subtype.val (hpow₀ a ha w hw)
  have hNC : ∀ g ∈ N, ∀ x ∈ Cₐ, g * x * g⁻¹ ∈ Cₐ := by
    intro g hg
    rintro _ ⟨a, ha, rfl⟩
    have hgF : g ∈ normalizer (Fs : Set K) := hN hg
    have hφ := Subgroup.normalizerMonoidHom_apply_apply_coe Fs ⟨g, hgF⟩ a
    refine ⟨_, CFSG.SectionRank.Ccomm.char_apply_mem hchar (Fs.normalizerMonoidHom ⟨g, hgF⟩) ha, ?_⟩
    simpa using hφ
  have hNCn : ∀ g ∈ N, g ∈ normalizer (Cₐ : Set K) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hNC g hg x hx, fun hx => ?_⟩
    have := hNC g⁻¹ (N.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  let Ω : Subgroup K :=
    { carrier := {x | x ∈ Cₐ ∧ x ^ f = 1}
      mul_mem' := by
        rintro x y ⟨hx, hxf⟩ ⟨hy, hyf⟩
        refine ⟨mul_mem hx hy, ?_⟩
        rw [pow_mul_of_central hf hf2 hcl hpow hx hy, hxf, hyf, one_mul]
      one_mem' := ⟨one_mem _, one_pow _⟩
      inv_mem' := by
        rintro x ⟨hx, hxf⟩
        exact ⟨inv_mem hx, by rw [inv_pow, hxf, inv_one]⟩ }
  have hΩmem : ∀ x, x ∈ Ω ↔ x ∈ Cₐ ∧ x ^ f = 1 := fun x => Iff.rfl
  have hNΩ : ∀ g ∈ N, ∀ x ∈ Ω, g * x * g⁻¹ ∈ Ω := by
    intro g hg x hx
    obtain ⟨hxC, hxf⟩ := (hΩmem x).mp hx
    refine (hΩmem _).mpr ⟨hNC g hg x hxC, ?_⟩
    rw [conj_pow, hxf]
    group
  have hNΩn : N ≤ normalizer (Ω : Set K) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hNΩ g hg x hx, fun hx => ?_⟩
    have := hNΩ g⁻¹ (N.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  refine ⟨Ω, ⟨?_, ?_, ?_, hNΩn, ?_⟩⟩
  · exact fun x hx => hCₐle ((hΩmem x).mp hx).1
  · exact fun x hx => ((hΩmem x).mp hx).2
  · intro x hx y hy w hw
    exact hcl x ((hΩmem x).mp hx).1 y ((hΩmem y).mp hy).1 w ((hΩmem w).mp hw).1
  · intro t ht n htn htriv x hx
    have hΩC : Ω ≤ Cₐ := fun x hx => ((hΩmem x).mp hx).1
    have hΩt : ∀ y ∈ Ω, t * y = y * t := by
      have hfr : (⁅Ω, Ω⁆).subgroupOf Ω ≤ frattini ↥Ω := by
        have := commutator_pow_le_frattini (f := f) (C := Ω) (hCₐp.to_le hΩC)
        exact fun x hx => this (Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))
      exact eq_of_trivial_on_quotient_pElt hp hpf (hCₐp.to_le hΩC)
        (commutator_le_self Ω)
        (fun x hx m hm => by
          have hxn : x ∈ normalizer ((⁅Ω, Ω⁆ : Subgroup K) : Set K) :=
            normalizer_le_normalizer_commutator Ω (le_normalizer hx)
          exact (mem_normalizer_iff.mp hxn m).mp hm)
        hfr htn (hNΩn ht) (normalizer_le_normalizer_commutator Ω (hNΩn ht)) htriv
    have hCt : ∀ y ∈ Cₐ, t * y = y * t :=
      fixed_of_pow_fixed hf2 hp hpf hCₐp hcl hpow htn (hNCn t ht)
        (fun y hy hyf => hΩt y ((hΩmem y).mpr ⟨hy, hyf⟩))
    exact centralizes_of_critical_pElt hp hpf hFs C₀ hC₀full htn (hN ht) hCt x hx

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2
