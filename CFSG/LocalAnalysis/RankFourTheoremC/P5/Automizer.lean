module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Strong
import CFSG.LocalAnalysis.RankFourTheoremC.PPointCover
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFusion
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.QK

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace BorelDataP

variable {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {x : G} {n : ℕ}
  {f : GaloisField p n → G} {W : Subgroup G}

theorem Acts.squares (hB : BorelDataP p P M x f W) (hS : PtShape p P x) {O : Subgroup G}
    (hO : ¬ p ∣ Nat.card O) (hOM : M ≤ normalizer (O : Set G)) (hOle : O ≤ M)
    (hQM : hB.QK ≤ M) (hRM : M ≤ normalizer ((hB.QK ⊔ O : Subgroup G) : Set G))
    (hCM : centralizer (hB.QK : Set G) ≤ M)
    {m : G} (hm : m ∈ M) {ψ : GaloisField p n → GaloisField p n}
    (hψ : Acts (f := f) O m ψ) (a : (GaloisField p n)ˣ) :
    ∃ b : (GaloisField p n)ˣ, ∀ t, ψ ((a : GaloisField p n) ^ 2 * t) =
      (b : GaloisField p n) ^ 2 * ψ t := by
  have hQO : hB.QK ≤ normalizer (O : Set G) := hQM.trans hOM
  obtain ⟨r, hr, m', hm', hrm⟩ :=
    exists_mul_normalizer_of_isSylowOf (hB.isSylowOf_QK hO hQO) hRM hm
  have hrM : r ∈ M := by
    have : (hB.QK ⊔ O) ≤ M := sup_le hQM hOle
    exact this hr
  have hm'M : m' ∈ M := by
    have : m' = r⁻¹ * m := by rw [hrm]; group
    rw [this]
    exact M.mul_mem (M.inv_mem hrM) hm
  have hψ' : Acts (f := f) O m' ψ := by
    intro t
    obtain ⟨o, ho, h⟩ := hψ t
    have hg : f (ψ t) ∈ hB.QK ⊔ O := Subgroup.mem_sup_left (hB.f_mem_QK _)
    have hrinv : r⁻¹ ∈ hB.QK ⊔ O := Subgroup.inv_mem _ hr
    have hcomm := hB.comm_mem_QK_sup hQO (Subgroup.inv_mem _ hg) hrinv
    have hro : r⁻¹ * o * r ∈ O :=
      (mem_normalizer_iff.mp (hOM (M.inv_mem hrM)) o).mp ho |> fun h' => by simpa using h'
    refine ⟨(f (ψ t))⁻¹ * r⁻¹ * f (ψ t) * r * (r⁻¹ * o * r), O.mul_mem ?_ hro, ?_⟩
    · simpa [mul_assoc] using hcomm
    · have e1 : m' * f t * m'⁻¹ = r⁻¹ * (m * f t * m⁻¹) * r := by rw [hrm]; group
      rw [e1, h]
      group
  obtain ⟨c, hcC, hcm⟩ := exists_centralizer_mul_mem_normalizer_zpowers_p hS.weak hB.x_pow
    (fun e he => hB.QK_comm_x he) hm'
  have hcM : c ∈ M := hCM hcC
  have hcQ : ∀ q ∈ hB.QK, c * q = q * c := fun q hq => (mem_centralizer_iff.mp hcC q hq).symm
  set n₀ : G := c * m' with hn₀
  have hn₀Q : n₀ ∈ normalizer (hB.QK : Set G) :=
    Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer (hB.QK : Set G) hcC) hm'
  have hψ₀ : Acts (f := f) O n₀ ψ := by
    intro t
    obtain ⟨o, ho, h⟩ := hψ' t
    refine ⟨c * o * c⁻¹, (mem_normalizer_iff.mp (hOM hcM) o).mp ho, ?_⟩
    have hcf : c * f (ψ t) = f (ψ t) * c := hcQ _ (hB.f_mem_QK _)
    calc n₀ * f t * n₀⁻¹ = c * (m' * f t * m'⁻¹) * c⁻¹ := by simp only [hn₀]; group
      _ = c * (f (ψ t) * o) * c⁻¹ := by rw [h]
      _ = (c * f (ψ t)) * o * c⁻¹ := by group
      _ = f (ψ t) * (c * o * c⁻¹) := by rw [hcf]; group
  have hexact : ∀ t, n₀ * f t * n₀⁻¹ = f (ψ t) := by
    intro t
    obtain ⟨o, ho, h⟩ := hψ₀ t
    have hmem : n₀ * f t * n₀⁻¹ ∈ hB.QK :=
      (mem_normalizer_iff.mp hn₀Q (f t)).mp (hB.f_mem_QK t)
    obtain ⟨s, hs⟩ := hB.mem_QK.mp hmem
    have hst : s = ψ t := hB.eq_of_f_mul_mem hO (O := O) (o := 1) (o' := o) O.one_mem ho hQO
      (by rw [mul_one, hs, h])
    rw [← hs, hst]
  obtain ⟨R, K, d, hfacts, hd, ⟨eK⟩, hρ, hsurj, hsq, htorK, -⟩ := hB.reduced
  have hred := hfacts.red
  have hCmem : ∀ t, f t ∈ centralizer ({x} : Set G) := fun t =>
    mem_centralizer_singleton_iff.mpr (hB.f_comm t)
  obtain ⟨e, he⟩ := exists_redCent_mulEquiv p (x := x) (n := n₀) hcm
  set ρ := QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
    (G := centralizer ({x} : Set G)) p) with hρdef
  have hact : ∀ t, e (ρ ⟨f t, hCmem t⟩) = ρ ⟨f (ψ t), hCmem _⟩ := by
    intro t
    have hnc : n₀ * f t * n₀⁻¹ ∈ centralizer ({x} : Set G) := by
      rw [hexact t]; exact hCmem _
    refine (he (f t) (hCmem t) hnc).trans ?_
    congr 1
    exact Subtype.ext (hexact t)
  have hKe : K.map e.toMonoidHom = K :=
    hred.unique _ ((CFSG.ComponentClassification.LocalComponents.equiv_iff e K).mpr hred.component)
  set Tp : Subgroup (RedCent p x) := (R : Subgroup (RedCent p x)) ⊓ K with hTp
  have hTpe : Tp.map e.toMonoidHom ≤ Tp := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨t, hc, rfl⟩ := hsurj y hy
    show e (ρ ⟨f t, hc⟩) ∈ Tp
    have h1 : e (ρ ⟨f t, hc⟩) = ρ ⟨f (ψ t), hCmem _⟩ := hact t
    rw [h1]
    exact (hρ (ψ t)).choose_spec.1
  have hTpe' : Tp.map e.toMonoidHom = Tp :=
    Subgroup.eq_of_le_of_card_ge hTpe (by rw [Subgroup.card_map_of_injective e.injective])
  have hinj : ∀ s t : GaloisField p n, ρ ⟨f s, hCmem s⟩ = ρ ⟨f t, hCmem t⟩ → s = t := by
    intro s t hst
    by_contra hne
    have hne' : s - t ≠ 0 := sub_ne_zero.mpr hne
    have h1 : ρ ⟨f (s - t), hCmem _⟩ = 1 := by
      have : (⟨f (s - t), hCmem _⟩ : centralizer ({x} : Set G)) =
          ⟨f s, hCmem s⟩ * ⟨f t, hCmem t⟩⁻¹ := Subtype.ext (by
        change f (s - t) = f s * (f t)⁻¹
        rw [sub_eq_add_neg, hB.f_add, hB.f_neg])
      rw [this, map_mul, map_inv, hst]
      exact mul_inv_cancel _
    exact (hρ (s - t)).choose_spec.2 hne' h1
  obtain ⟨τ, hτK, hτN, hτ⟩ := htorK a
  set σ : RedCent p x := e τ with hσ
  have hσK : σ ∈ K := by
    have : e τ ∈ K.map e.toMonoidHom := ⟨τ, hτK, rfl⟩
    rwa [hKe] at this
  have hσN : σ ∈ normalizer ((Tp : Subgroup (RedCent p x)) : Set (RedCent p x)) := by
    have h1 : e τ ∈ (normalizer (Tp : Set (RedCent p x))).map e.toMonoidHom := ⟨τ, hτN, rfl⟩
    rw [Subgroup.map_equiv_normalizer_eq, hTpe'] at h1
    exact h1
  obtain ⟨b, hb⟩ := hsq σ hσK hσN
  refine ⟨b, fun t' => ?_⟩
  apply hinj (ψ ((a : GaloisField p n) ^ 2 * t')) ((b : GaloisField p n) ^ 2 * ψ t')
  calc ρ ⟨f (ψ ((a : GaloisField p n) ^ 2 * t')), hCmem _⟩
      = e (ρ ⟨f ((a : GaloisField p n) ^ 2 * t'), hCmem _⟩) := (hact _).symm
    _ = e (τ * ρ ⟨f t', hCmem t'⟩ * τ⁻¹) := by rw [hτ t' (hCmem _) (hCmem _)]
    _ = σ * ρ ⟨f (ψ t'), hCmem _⟩ * σ⁻¹ := by rw [map_mul, map_mul, map_inv, hact t']
    _ = ρ ⟨f ((b : GaloisField p n) ^ 2 * ψ t'), hCmem _⟩ := hb (ψ t') _ _

end BorelDataP

end CFSG.LocalAnalysis.RankFourTheoremC.P5
