module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Sec

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

namespace S289G

variable {X : Type} [Group X]

@[expose] def StarFrameGenAll (Φ : Set (Subgroup X)) (L : Subgroup X) : Prop :=
  ∀ a : X, IsUniqueInvolution L a →
    Subgroup.centralizer ({a} : Set X) ⊔
      (⨆ (L' : Subgroup X) (_ : L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L) (b : X)
        (_ : IsUniqueInvolution L' b),
          Subgroup.centralizer ({b} : Set X) ⊔ Subgroup.centralizer ({a * b} : Set X)) = ⊤

theorem StarFrameGenAll.of_pair {Φ : Set (Subgroup X)} {L L' : Subgroup X}
    (hst : L' ∈ omegaStarNbr Φ L) (hn : L' ∉ omegaNbr Φ L) {b : X}
    (hb : IsUniqueInvolution L' b)
    (h : ∀ a : X, IsUniqueInvolution L a →
      Subgroup.centralizer ({a} : Set X) ⊔ Subgroup.centralizer ({b} : Set X) ⊔
        Subgroup.centralizer ({a * b} : Set X) = ⊤) :
    StarFrameGenAll Φ L := by
  intro a ha
  rw [eq_top_iff, ← h a ha]
  refine sup_le (sup_le le_sup_left ?_) ?_
  · exact le_sup_of_le_right (le_iSup₂_of_le L' ⟨hst, hn⟩ (le_iSup₂_of_le b hb le_sup_left))
  · exact le_sup_of_le_right (le_iSup₂_of_le L' ⟨hst, hn⟩ (le_iSup₂_of_le b hb le_sup_right))

theorem centralizer_conj_le {H : Subgroup X} {a g : X}
    (hC : Subgroup.centralizer ({a} : Set X) ≤ H) (hg : g ∈ H) :
    Subgroup.centralizer ({g * a * g⁻¹} : Set X) ≤ H := by
  intro y hy
  have hy' : y * (g * a * g⁻¹) = g * a * g⁻¹ * y := Subgroup.mem_centralizer_singleton_iff.mp hy
  have h1 : g⁻¹ * y * g ∈ Subgroup.centralizer ({a} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * y * g * a = g⁻¹ * (y * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * a * g⁻¹ * y) * g := by rw [hy']
      _ = a * (g⁻¹ * y * g) := by group
  have h2 := H.mul_mem (H.mul_mem hg (hC h1)) (H.inv_mem hg)
  rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h2

theorem le_centralizer_of_isUniqueInvolution {M : Subgroup X} {m : X}
    (hm : IsUniqueInvolution M m) : M ≤ Subgroup.centralizer ({m} : Set X) := by
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e := hm.conj_eq (conjSub_eq_self_of_mem hk)
  calc k * m = k * m * k⁻¹ * k := by group
    _ = m * k := by rw [e]

theorem centralizer_eq_of_mul_mem_center {m n : X} (hn : n * n = 1)
    (hc : m * n ∈ Subgroup.center X) :
    Subgroup.centralizer ({n} : Set X) = Subgroup.centralizer ({m} : Set X) := by
  ext y
  simp only [Subgroup.mem_centralizer_singleton_iff]
  have hcy : y * (m * n) = m * n * y := Subgroup.mem_center_iff.mp hc y
  have hm : m = m * n * n := by rw [mul_assoc, hn, mul_one]
  have e1 : y * m = m * n * (y * n) := by
    calc y * m = y * (m * n * n) := by rw [← hm]
      _ = y * (m * n) * n := by simp only [mul_assoc]
      _ = m * n * y * n := by rw [hcy]
      _ = m * n * (y * n) := by simp only [mul_assoc]
  have e2 : m * y = m * n * (n * y) := by
    calc m * y = m * n * n * y := by rw [← hm]
      _ = m * n * (n * y) := by simp only [mul_assoc]
  rw [e1, e2, mul_right_inj]

theorem normalizer_eq_centralizer {r : ℕ} {Φ : Set (Subgroup X)} (h : TypeRFam r Φ)
    {M : Subgroup X} (hM : M ∈ Φ) {m : X} (hm : IsUniqueInvolution M m) :
    Subgroup.normalizer (M : Set X) = Subgroup.centralizer ({m} : Set X) := by
  refine le_antisymm (fun g hg => ?_) (h.tight M hM m hm)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e := hm.conj_eq (mem_normalizer_iff_conjSub_eq.mp hg)
  calc g * m = g * m * g⁻¹ * g := by group
    _ = m * g := by rw [e]

theorem mem_omegaStarNbr_of_normalizer_eq {Φ : Set (Subgroup X)} {M N Q : Subgroup X}
    (e : Subgroup.normalizer (N : Set X) = Subgroup.normalizer (M : Set X)) (hQM : Q ≠ M)
    (hQ : Q ∈ omegaStarNbr Φ N) : Q ∈ omegaStarNbr Φ M := by
  obtain ⟨hQΦ, -, U, hU, hUQ, hUN⟩ := hQ
  exact ⟨hQΦ, hQM, U, hU, hUQ, by rw [← e]; exact hUN⟩

theorem starFrameGenAll_of_dstarConnected [Finite X] {r : ℕ} {Φ : Set (Subgroup X)}
    (h : TypeRFam r Φ) (hgen : omegaGen Φ = ⊤) (hcon : T3.DStarConnected Φ)
    (h284 : ∀ M ∈ Φ, ∀ N ∈ omegaNbr Φ M, ∀ m n : X, IsUniqueInvolution M m →
      IsUniqueInvolution N n → m * n ∈ Subgroup.center X)
    {L : Subgroup X} (hL : L ∈ Φ) : StarFrameGenAll Φ L := by
  intro a ha
  have hΩ := h.hyp
  have hcl := hΩ.conjInvariant
  set H : Subgroup X := Subgroup.centralizer ({a} : Set X) ⊔
      (⨆ (L' : Subgroup X) (_ : L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L) (b : X)
        (_ : IsUniqueInvolution L' b),
          Subgroup.centralizer ({b} : Set X) ⊔ Subgroup.centralizer ({a * b} : Set X)) with hH
  have hCa : Subgroup.centralizer ({a} : Set X) ≤ H := le_sup_left
  have hCb : ∀ L' ∈ omegaStarNbr Φ L, L' ∉ omegaNbr Φ L → ∀ b : X, IsUniqueInvolution L' b →
      Subgroup.centralizer ({b} : Set X) ≤ H := fun L' h1 h2 b hb =>
    le_sup_of_le_right (le_iSup₂_of_le L' ⟨h1, h2⟩ (le_iSup₂_of_le b hb le_sup_left))
  have hS1 : ∀ g ∈ H, ∀ m : X, IsUniqueInvolution (conjSub g L) m →
      Subgroup.centralizer ({m} : Set X) ≤ H := by
    intro g hg m hm
    rw [hm.eq (ha.conj g)]
    exact centralizer_conj_le hCa hg
  have hS2 : ∀ g ∈ H, ∀ M' ∈ omegaStarNbr Φ (conjSub g L), M' ∉ omegaNbr Φ (conjSub g L) →
      ∀ m' : X, IsUniqueInvolution M' m' → Subgroup.centralizer ({m'} : Set X) ≤ H := by
    intro g hg M' hst hn m' hm'
    have hst' : conjSub g⁻¹ M' ∈ omegaStarNbr Φ L := by
      have h1 := Asc77.omegaStarNbr_conj hcl hst g⁻¹
      rwa [conjSub_inv_conjSub] at h1
    have hn' : conjSub g⁻¹ M' ∉ omegaNbr Φ L := by
      intro h1
      have h2 := Asc77.omegaNbr_conj hcl h1 g
      rw [conjSub_conjSub_inv] at h2
      exact hn h2
    have h3 := centralizer_conj_le (hCb _ hst' hn' _ (hm'.conj g⁻¹)) hg
    rwa [show g * (g⁻¹ * m' * g⁻¹⁻¹) * g⁻¹ = m' by group] at h3
  have hS3 : ∀ g ∈ H, ∀ M' ∈ omegaStarNbr Φ (conjSub g L), M' ∉ omegaNbr Φ (conjSub g L) →
      ∃ g' ∈ H, conjSub g' L = M' := by
    intro g hg M' hst hn
    have hM : conjSub g L ∈ Φ := hcl g L hL
    obtain ⟨m', hm'⟩ := Sec6Gen.exists_uniqueInvolution hΩ hst.1
    have hm := ha.conj g
    obtain ⟨k, hk, hkM⟩ := TL4.aEmpty_of_noTwins hΩ hM (h.noTwins _ hM) M' hst hn _ _ hm hm'
    have hkH : k ∈ H :=
      (sup_le (inf_le_left.trans ((le_centralizer_of_isUniqueInvolution hm).trans
          (hS1 g hg _ hm)))
        (inf_le_left.trans ((le_centralizer_of_isUniqueInvolution hm').trans
          (hS2 g hg M' hst hn m' hm')))) hk
    exact ⟨k * g, H.mul_mem hkH hg, by rw [conjSub_mul, hkM]⟩
  have hcent : ∀ g ∈ H, ∀ N ∈ omegaNbr Φ (conjSub g L), ∀ n : X, IsUniqueInvolution N n →
      Subgroup.centralizer ({n} : Set X) = Subgroup.centralizer ({g * a * g⁻¹} : Set X) :=
    fun g _ N hN n hn => centralizer_eq_of_mul_mem_center hn.sq
      (h284 _ (hcl g L hL) N hN _ n (ha.conj g) hn)
  have hnormN : ∀ g ∈ H, ∀ N ∈ omegaNbr Φ (conjSub g L), Subgroup.normalizer (N : Set X) =
      Subgroup.normalizer ((conjSub g L : Subgroup X) : Set X) := by
    intro g hg N hN
    obtain ⟨n, hn⟩ := Sec6Gen.exists_uniqueInvolution hΩ hN.1
    rw [normalizer_eq_centralizer h hN.1 hn, normalizer_eq_centralizer h (hcl g L hL) (ha.conj g),
      hcent g hg N hN n hn]
  have stepS : ∀ g ∈ H, ∀ Q ∈ omegaStarNbr Φ (conjSub g L),
      (∃ g' ∈ H, conjSub g' L = Q) ∨ ∃ g' ∈ H, Q ∈ omegaNbr Φ (conjSub g' L) := by
    intro g hg Q hQ
    by_cases hn : Q ∈ omegaNbr Φ (conjSub g L)
    · exact Or.inr ⟨g, hg, hn⟩
    · exact Or.inl (hS3 g hg Q hQ hn)
  have closed : ∀ P Q : Subgroup X,
      ((∃ g ∈ H, conjSub g L = P) ∨ ∃ g ∈ H, P ∈ omegaNbr Φ (conjSub g L)) →
      dstarAdj Φ P Q →
        (∃ g ∈ H, conjSub g L = Q) ∨ ∃ g ∈ H, Q ∈ omegaNbr Φ (conjSub g L) := by
    intro P Q hP hPQ
    have hPΦ : P ∈ Φ := by
      rcases hP with ⟨g, -, rfl⟩ | ⟨g, -, hN⟩
      · exact hcl g L hL
      · exact hN.1
    have hQ : Q ∈ omegaStarNbr Φ P := by
      rcases hPQ.2 with h1 | h1
      · exact h1
      · exact Q3T6.Mu.omegaStarNbr_symm hΩ hPQ.1 hPΦ h1
    rcases hP with ⟨g, hg, rfl⟩ | ⟨g, hg, hN⟩
    · exact stepS g hg Q hQ
    · by_cases hQM : Q = conjSub g L
      · exact Or.inl ⟨g, hg, hQM.symm⟩
      · exact stepS g hg Q (mem_omegaStarNbr_of_normalizer_eq (hnormN g hg P hN) hQM hQ)
  have hallT : ∀ Q : Subgroup X, Relation.ReflTransGen (dstarAdj Φ) L Q →
      (∃ g ∈ H, conjSub g L = Q) ∨ ∃ g ∈ H, Q ∈ omegaNbr Φ (conjSub g L) := by
    intro Q hpath
    induction hpath with
    | refl => exact Or.inl ⟨1, H.one_mem, conjSub_one L⟩
    | tail _ hstep ih => exact closed _ _ ih hstep
  have hmemH : ∀ Q ∈ Φ, Q ≤ H := by
    intro Q hQ
    obtain ⟨q, hq⟩ := Sec6Gen.exists_uniqueInvolution hΩ hQ
    rcases hallT Q (hcon L hL Q hQ) with ⟨g, hg, rfl⟩ | ⟨g, hg, hN⟩
    · exact (le_centralizer_of_isUniqueInvolution hq).trans (hS1 g hg q hq)
    · exact (le_centralizer_of_isUniqueInvolution hq).trans
        ((hcent g hg Q hN q hq).le.trans (hS1 g hg _ (ha.conj g)))
  rw [eq_top_iff, ← hgen]
  exact iSup₂_le hmemH

end S289G

end CFSG.ClassicalInvolution.Q3.TL4
