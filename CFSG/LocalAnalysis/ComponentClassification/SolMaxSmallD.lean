module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallC
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallB

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

variable {X : Type} [Group X]

theorem le_coreActionKernel_of_diagonal_pump [Finite X] {c t s j : X} {M T X₀ : Subgroup X}
    (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))))
    (htC : t ∈ centralizer ({c} : Set X)) (htt : t * t = 1)
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M)
    (ψ : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin 7))
    (hTM : T ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom) (hTC : T ≤ centralizer ({t} : Set X))
    (hTperf : ⁅T, T⁆ = T) (hres : CatalogueBPrimeJoin.primeResidual 2 ↥T = ⊤)
    (χ : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 7))
    (hsN : s ∈ normalizer (M : Set X)) (hs2 : s * s = 1)
    (hsK : s ∉ UnbalancedLayer.coreActionKernel M) (hj : j ∈ T)
    (hsj : s * j⁻¹ ∈ UnbalancedLayer.coreActionKernel T)
    (hodd : Odd (Nat.card X₀)) (hX₀N : X₀ ≤ normalizer (M : Set X))
    (hX₀s : X₀ ≤ centralizer ({s} : Set X)) (htX : ∀ x ∈ X₀, t * x * t⁻¹ ∈ X₀)
    (hX₀n : ∀ g ∈ centralizer ({s} : Set X) ⊓ centralizer ({c} : Set X), ∀ x ∈ X₀,
      g * x * g⁻¹ ∈ X₀)
    (hY : ∀ y ∈ X₀, t * y = y * t → y ∈ UnbalancedLayer.coreActionKernel T) :
    X₀ ≤ UnbalancedLayer.coreActionKernel M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hMC hMpc
  set Mt := M.map (MulAut.conj t).toMonoidHom with hMtdef
  obtain ⟨hMtC, hMtpc⟩ := isPComponent_conj hMC hMpc htC
  have hMtK : Mt ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMC hMtC hMpc hMtpc (Ne.symm hne)
  have hMtN : Mt ≤ normalizer (M : Set X) := fun z hz => (hMtK hz).1
  have hTN : T ≤ normalizer (M : Set X) := hTM.trans (sup_le le_normalizer hMtN)
  obtain ⟨ρ, hρ⟩ := exists_isPermActionZ (N := M) (by norm_num) (by norm_num) ψ
  let ρX : X → Perm (Fin 7) := fun g => if h : g ∈ normalizer (M : Set X) then ρ ⟨g, h⟩ else 1
  have hρX : ∀ (g : X) (hg : g ∈ normalizer (M : Set X)), ρX g = ρ ⟨g, hg⟩ :=
    fun g hg => by simp [ρX, hg]
  have hρXmul : ∀ g ∈ normalizer (M : Set X), ∀ h ∈ normalizer (M : Set X),
      ρX (g * h) = ρX g * ρX h := by
    intro g hg h hh
    rw [hρX _ (mul_mem hg hh), hρX g hg, hρX h hh, ← map_mul]
    rfl
  have hρXinv : ∀ g ∈ normalizer (M : Set X), ρX g⁻¹ = (ρX g)⁻¹ := by
    intro g hg
    rw [hρX _ (inv_mem hg), hρX g hg, ← map_inv]
    rfl
  have hne' : ∃ l : ↥T, ρ (inclusion hTN l) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply not_le_coreActionKernel_of_pump hMC hMpc htC hTM hTC hTperf
      (nontrivial_coreQuot_of_seven χ) hne
    intro l hl
    exact hρ.mem_coreActionKernel hM (hTN hl) (hall ⟨l, hl⟩)
  obtain ⟨hsurj, hTA, hO⟩ := image_of_seven hTN hTperf hres χ hne'
  have hcak : ∀ y ∈ normalizer (M : Set X), y ∈ UnbalancedLayer.coreActionKernel T →
      ρX y = 1 := by
    intro y hy hyT
    rw [hρX y hy]
    exact eq_one_of_mem_cak_of_image hTN hsurj hO hy hyT
  have hρMt : ∀ z ∈ Mt, ρX z = 1 := by
    intro z hz
    rw [hρX z (hMtN hz)]
    exact hρ.eq_one_of_mem_coreActionKernel (by norm_num) (hMtK hz)
  have hρM : ∀ m : ↥M, ρX m = (ψ (m : ↥M ⧸ Open.fusionZStar ↥M) : Perm (Fin 7)) := by
    intro m
    rw [hρX m (le_normalizer m.2)]
    exact hρ.apply_of_mem (by norm_num) m
  have hcakM : ∀ g ∈ normalizer (M : Set X), ρX g = 1 →
      g ∈ UnbalancedLayer.coreActionKernel M := by
    intro g hg h1
    rw [hρX g hg] at h1
    exact hρ.mem_coreActionKernel hM hg h1
  have hjN : j ∈ normalizer (M : Set X) := hTN hj
  have hρs : ρX s = ρX j := by
    have hsjN : s * j⁻¹ ∈ normalizer (M : Set X) := mul_mem hsN (inv_mem hjN)
    have h1 := hcak _ hsjN hsj
    have h2 : s = s * j⁻¹ * j := by group
    rw [h2, hρXmul _ hsjN _ hjN, h1, one_mul]
  have hφA : ρX s ∈ alternatingGroup (Fin 7) := by
    rw [hρs, hρX j hjN]
    exact hTA ⟨j, hj⟩
  have hφ2 : ρX s * ρX s = 1 := by
    rw [← hρXmul s hsN s hsN, hs2, hρX 1 (one_mem _)]
    exact map_one ρ
  have hφ1 : ρX s ≠ 1 := fun h => hsK (hcakM s hsN h)
  have hcommφ : ∀ x ∈ X₀, ρX x * ρX s = ρX s * ρX x := by
    intro x hx
    have hxs : x * s = s * x := mem_centralizer_singleton_iff.mp (hX₀s hx)
    rw [← hρXmul x (hX₀N hx) s hsN, ← hρXmul s hsN x (hX₀N hx), hxs]
  set P : Subgroup (Perm (Fin 7)) := (X₀.subgroupOf (normalizer (M : Set X))).map ρ with hPdef
  have hPmem : ∀ x ∈ X₀, ρX x ∈ P := by
    intro x hx
    rw [hρX x (hX₀N hx)]
    exact ⟨⟨x, hX₀N hx⟩, hx, rfl⟩
  have hPodd : Odd (Nat.card P) := by
    have h1 : Nat.card P ∣ Nat.card (X₀.subgroupOf (normalizer (M : Set X))) :=
      card_map_dvd _ _
    rw [Nat.card_congr (subgroupOfEquivOfLe hX₀N).toEquiv] at h1
    exact hodd.of_dvd_nat h1
  have hPφ : ∀ g ∈ P, g * ρX s = ρX s * g := by
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    have h1 := hcommφ x hx
    rwa [hρX x hxN] at h1
  have hcomm : ∀ x ∈ X₀, ∀ y ∈ X₀, ρX x * ρX y = ρX y * ρX x := fun x hx y hy =>
    commute_of_odd_of_commute_seven hφA hφ2 hφ1 hPodd hPφ (hPmem x hx) (hPmem y hy)
  set K₁ : Subgroup X := ρ.ker.map (normalizer (M : Set X)).subtype with hK₁def
  have hK₁ : ∀ g, g ∈ K₁ ↔ g ∈ normalizer (M : Set X) ∧ ρX g = 1 := by
    intro g
    constructor
    · rintro ⟨⟨g', hg'⟩, h1, rfl⟩
      exact ⟨hg', by change ρX g' = 1; rw [hρX g' hg']; exact h1⟩
    · rintro ⟨hg, h1⟩
      rw [hρX g hg] at h1
      exact ⟨⟨g, hg⟩, h1, rfl⟩
  set K' : Subgroup X := K₁ ⊓ K₁.comap (MulAut.conj t).toMonoidHom with hK'def
  have hK' : ∀ g, g ∈ K' ↔ (g ∈ normalizer (M : Set X) ∧ ρX g = 1) ∧
      (t * g * t⁻¹ ∈ normalizer (M : Set X) ∧ ρX (t * g * t⁻¹) = 1) := by
    intro g
    rw [hK'def, mem_inf, mem_comap, hK₁, hK₁]
    rfl
  have httg : ∀ g : X, t * (t * g * t⁻¹) * t⁻¹ = g := by
    intro g
    calc t * (t * g * t⁻¹) * t⁻¹ = (t * t) * g * (t * t)⁻¹ := by group
      _ = g := by rw [htt]; group
  have htK' : ∀ k ∈ K', t * k * t⁻¹ ∈ K' := by
    intro k hk
    rw [hK'] at hk ⊢
    obtain ⟨h1, h2⟩ := hk
    rw [httg k]
    exact ⟨h2, h1⟩
  have hC' : ∀ y ∈ X₀, t * y = y * t → y ∈ K' := by
    intro y hy hyt
    have htyt : t * y * t⁻¹ = y := by rw [hyt]; group
    have h1 := hcak y (hX₀N hy) (hY y hy hyt)
    rw [hK', htyt]
    exact ⟨⟨hX₀N hy, h1⟩, ⟨hX₀N hy, h1⟩⟩
  have hanti : ∀ x ∈ X₀, ρX (t * x * t⁻¹) = (ρX x)⁻¹ := by
    intro x hx
    have hxN := hX₀N hx
    have htx := htX x hx
    have htxN := hX₀N htx
    have hwX : x * (t * x * t⁻¹) ∈ X₀ := mul_mem hx htx
    have hwN := hX₀N hwX
    have htw : t * (x * (t * x * t⁻¹)) * t⁻¹ = (t * x * t⁻¹) * x := by
      calc t * (x * (t * x * t⁻¹)) * t⁻¹ = (t * x * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) := by
            group
        _ = (t * x * t⁻¹) * x := by rw [httg x]
    have hρw : ρX (x * (t * x * t⁻¹)) = ρX x * ρX (t * x * t⁻¹) := hρXmul x hxN _ htxN
    have hρtw : ρX (t * (x * (t * x * t⁻¹)) * t⁻¹) = ρX x * ρX (t * x * t⁻¹) := by
      rw [htw, hρXmul _ htxN x hxN]
      exact hcomm _ htx x hx
    have htwN : t * (x * (t * x * t⁻¹)) * t⁻¹ ∈ normalizer (M : Set X) :=
      hX₀N (htX _ hwX)
    have hwK : x * (t * x * t⁻¹) ∈ K' := by
      refine mem_of_conj_mem hodd htt htX htK' hC' hwX ?_
      rw [hK']
      set w := x * (t * x * t⁻¹) with hw
      have hm : w⁻¹ * (t * w * t⁻¹) ∈ normalizer (M : Set X) := mul_mem (inv_mem hwN) htwN
      have htm : t * (w⁻¹ * (t * w * t⁻¹)) * t⁻¹ = (t * w * t⁻¹)⁻¹ * w := by
        calc t * (w⁻¹ * (t * w * t⁻¹)) * t⁻¹ =
            (t * w * t⁻¹)⁻¹ * (t * (t * w * t⁻¹) * t⁻¹) := by group
          _ = (t * w * t⁻¹)⁻¹ * w := by rw [httg w]
      refine ⟨⟨hm, ?_⟩, ⟨?_, ?_⟩⟩
      · rw [hρXmul _ (inv_mem hwN) _ htwN, hρXinv w hwN, hρw, hρtw]
        group
      · rw [htm]
        exact mul_mem (inv_mem htwN) hwN
      · rw [htm, hρXmul _ (inv_mem htwN) _ hwN, hρXinv _ htwN, hρw, hρtw]
        group
    have h1 := ((hK' _).mp hwK).1.2
    rw [hρw] at h1
    exact eq_inv_of_mul_eq_one_right h1
  by_contra hX₀K
  obtain ⟨x₀, hx₀, hx₀K⟩ : ∃ x ∈ X₀, x ∉ UnbalancedLayer.coreActionKernel M := by
    by_contra h
    push Not at h
    exact hX₀K h
  have hx₀N := hX₀N hx₀
  have ha1 : ρX x₀ ≠ 1 := fun h => hx₀K (hcakM x₀ hx₀N h)
  have haodd : Odd (orderOf (ρX x₀)) := by
    have h1 : orderOf (ρX x₀) ∣ Nat.card P := by
      rw [← Subgroup.orderOf_mk (ρX x₀) (hPmem x₀ hx₀)]
      exact orderOf_dvd_natCard _
    exact hPodd.of_dvd_nat h1
  obtain ⟨g, hgA, hgg, hga⟩ :=
    exists_sq_eq_not_commute hφA hφ2 hφ1 ha1 haodd (hcommφ x₀ hx₀)
  have hlift : ∀ π ∈ alternatingGroup (Fin 7), ∃ m : ↥M, ρX m = π := by
    intro π hπ
    obtain ⟨q, hq⟩ := ψ.surjective ⟨π, hπ⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨m, by rw [hρM m, hq]⟩
  obtain ⟨m', hm'⟩ := hlift g hgA
  obtain ⟨m₁, hm₁⟩ := hlift (ρX s) hφA
  have hm'N : (m' : X) ∈ normalizer (M : Set X) := le_normalizer m'.2
  have hm₁N : (m₁ : X) ∈ normalizer (M : Set X) := le_normalizer m₁.2
  have hkN : (m₁ : X)⁻¹ * s ∈ normalizer (M : Set X) := mul_mem (inv_mem hm₁N) hsN
  have hkK : (m₁ : X)⁻¹ * s ∈ UnbalancedLayer.coreActionKernel M := by
    refine hcakM _ hkN ?_
    rw [hρXmul _ (inv_mem hm₁N) _ hsN, hρXinv _ hm₁N, hm₁]
    group
  have hζZ : m' * m' * m₁⁻¹ ∈ Open.fusionZStar ↥M := by
    refine hρ.mem_fusionZStar_of_eq_one (by norm_num) _ ?_
    rw [← hρX _ (le_normalizer (m' * m' * m₁⁻¹).2)]
    change ρX ((m' : X) * m' * (m₁ : X)⁻¹) = 1
    rw [hρXmul _ (mul_mem hm'N hm'N) _ (inv_mem hm₁N), hρXmul _ hm'N _ hm'N, hρXinv _ hm₁N, hm',
      hm₁, hgg]
    group
  have hOM : (m' : X)⁻¹ * (s * m' * s⁻¹) ∈ coreNOf M := by
    set ζ : ↥M := m' * m' * m₁⁻¹ with hζdef
    set k := (m₁ : X)⁻¹ * s with hkdef
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hkK)).2 m' m'.2
    rw [inv_inv] at h1
    have h2 : (m' : X)⁻¹ * (ζ : X)⁻¹ * m' * ζ ∈ coreNOf M := by
      have h3 := (GSThmB.OddQuot.mem_fusionZStar_iff.mp (inv_mem hζZ)) m'⁻¹
      have h4 : (⁅ζ⁻¹, m'⁻¹⁆)⁻¹ = m'⁻¹ * ζ⁻¹ * m' * ζ := by
        rw [commutatorElement_def]
        group
      have h5 := inv_mem h3
      rw [h4] at h5
      exact ⟨_, h5, rfl⟩
    have h6 : (m₁ : X) * ((m' : X)⁻¹ * k * m' * k⁻¹) * (m₁ : X)⁻¹ ∈ coreNOf M :=
      (mem_normalizer_iff.mp (le_normalizer_pPrimeCore hm₁N) _).mp h1
    have hs : s = (m₁ : X) * k := by rw [hkdef]; group
    have hm₁' : (m₁ : X) = (ζ : X)⁻¹ * m' * m' := by
      change (m₁ : X) = ((m' : X) * m' * (m₁ : X)⁻¹)⁻¹ * m' * m'
      group
    have h7 : (m' : X)⁻¹ * (s * m' * s⁻¹) =
        ((m' : X)⁻¹ * (ζ : X)⁻¹ * m' * ζ) *
          ((m₁ : X) * ((m' : X)⁻¹ * k * m' * k⁻¹) * (m₁ : X)⁻¹) := by
      rw [hs, hm₁']
      group
    rw [h7]
    exact mul_mem h2 h6
  obtain ⟨k', hk'O, hk'c⟩ := exists_commute_of_mem_coset (odd_coreNOf M) hs2
    (fun o ho => (mem_normalizer_iff.mp (le_normalizer_pPrimeCore hsN) o).mp ho) hOM
  have hk'M : k' ∈ M := map_subtype_le _ hk'O
  have hhM : (m' : X) * k' ∈ M := mul_mem m'.2 hk'M
  have hhN : (m' : X) * k' ∈ normalizer (M : Set X) := le_normalizer hhM
  have hρh : ρX ((m' : X) * k') = g := by
    rw [hρXmul _ hm'N _ (le_normalizer hk'M), hm', hρX k' (le_normalizer hk'M),
      hρ.eq_one_of_mem_coreActionKernel (by norm_num) (coreNOf_le_coreActionKernel M hk'O),
      mul_one]
  have hht : t * ((m' : X) * k') * t⁻¹ ∈ Mt := ⟨_, hhM, rfl⟩
  have hhtN : t * ((m' : X) * k') * t⁻¹ ∈ normalizer (M : Set X) := hMtN hht
  have hhs : (m' : X) * k' ∈ centralizer ({s} : Set X) :=
    mem_centralizer_singleton_iff.mpr hk'c.symm
  have hhc : (m' : X) * k' ∈ centralizer ({c} : Set X) := hMC hhM
  set h := (m' : X) * k' with hhdef
  have hx₁ : h * x₀ * h⁻¹ ∈ X₀ := hX₀n h ⟨hhs, hhc⟩ x₀ hx₀
  have hρx₁ : ρX (h * x₀ * h⁻¹) = g * ρX x₀ * g⁻¹ := by
    rw [hρXmul _ (mul_mem hhN hx₀N) _ (inv_mem hhN), hρXmul _ hhN _ hx₀N, hρXinv _ hhN, hρh]
  have htx₀N : t * x₀ * t⁻¹ ∈ normalizer (M : Set X) := hX₀N (htX x₀ hx₀)
  have hρtx₁ : ρX (t * (h * x₀ * h⁻¹) * t⁻¹) = (ρX x₀)⁻¹ := by
    have htx₁ : t * (h * x₀ * h⁻¹) * t⁻¹ =
        (t * h * t⁻¹) * (t * x₀ * t⁻¹) * (t * h * t⁻¹)⁻¹ := by group
    rw [htx₁, hρXmul _ (mul_mem hhtN htx₀N) _ (inv_mem hhtN), hρXmul _ hhtN _ htx₀N,
      hρXinv _ hhtN, hρMt _ hht, hanti x₀ hx₀]
    group
  have h7 := hanti _ hx₁
  rw [hρtx₁, hρx₁] at h7
  have h8 : g * ρX x₀ * g⁻¹ = ρX x₀ := inv_inj.mp h7.symm
  apply hga
  calc g * ρX x₀ = g * ρX x₀ * g⁻¹ * g := by group
    _ = ρX x₀ * g := by rw [h8]

end CFSG.ComponentClassification.SolMax
