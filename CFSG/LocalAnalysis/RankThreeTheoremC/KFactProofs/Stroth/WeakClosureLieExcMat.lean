module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcWitness
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcFpf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Timmesfeld.ExceptionalOrders (zpowMatrix zpowMatrix_apply zpowMatrix_zpowMatrix zpowMatrix_one)
open scoped commutatorElement Matrix

variable {τ : Tag}

section Words

theorem wordMat_cw (x y : List (Fin τ.rank)) :
    wordMat τ (cw x y) =
      wordMat τ x * wordMat τ y * wordMat τ x.reverse * wordMat τ y.reverse := by
  simp only [cw, wordMat_append, mul_assoc]

theorem cw_reverse {n : ℕ} (x y : List (Fin n)) : (cw x y).reverse = cw y x := by
  simp [cw]

theorem wordMat_reverse_mul (l : List (Fin τ.rank)) : wordMat τ l.reverse * wordMat τ l = 1 := by
  rw [← weylMat_wp_inv l, ← weylMat_wp l, ← weylMat_mul, inv_mul_cancel, weylMat_one]

theorem wordMat_reverse_eq {l : List (Fin τ.rank)} {A B : List (List ℤ)}
    (hA : wordMat τ l = toMat τ.rank A) (hAB : lmul τ.rank A B = lid τ.rank) :
    wordMat τ l.reverse = toMat τ.rank B := by
  have h1 : toMat τ.rank A * toMat τ.rank B = 1 := by rw [← toMat_lmul, hAB, toMat_lid]
  calc wordMat τ l.reverse = wordMat τ l.reverse * (toMat τ.rank A * toMat τ.rank B) := by
        rw [h1, mul_one]
    _ = (wordMat τ l.reverse * wordMat τ l) * toMat τ.rank B := by rw [← mul_assoc, ← hA]
    _ = toMat τ.rank B := by rw [wordMat_reverse_mul, one_mul]

@[expose] def lcw (n : ℕ) (X X' Y Y' : List (List ℤ)) : List (List ℤ) :=
  lmul n (lmul n (lmul n X Y) X') Y'

@[expose] def ldc (n : ℕ) (A A' B B' C C' D D' : List (List ℤ)) : List (List ℤ) :=
  lcw n (lcw n A A' B B') (lcw n B B' A A') (lcw n C C' D D') (lcw n D D' C C')

@[expose] def ldcInv (n : ℕ) (A A' B B' C C' D D' : List (List ℤ)) : List (List ℤ) :=
  lcw n (lcw n C C' D D') (lcw n D D' C C') (lcw n A A' B B') (lcw n B B' A A')

theorem wordMat_cw_eq {x y : List (Fin τ.rank)} {X X' Y Y' : List (List ℤ)}
    (hX : wordMat τ x = toMat τ.rank X) (hX' : wordMat τ x.reverse = toMat τ.rank X')
    (hY : wordMat τ y = toMat τ.rank Y) (hY' : wordMat τ y.reverse = toMat τ.rank Y') :
    wordMat τ (cw x y) = toMat τ.rank (lcw τ.rank X X' Y Y') := by
  rw [wordMat_cw, hX, hX', hY, hY', lcw, toMat_lmul, toMat_lmul, toMat_lmul]

theorem wordMat_dc_eq {a b c d : List (Fin τ.rank)} {A A' B B' C C' D D' : List (List ℤ)}
    (hA : wordMat τ a = toMat τ.rank A) (hA' : wordMat τ a.reverse = toMat τ.rank A')
    (hB : wordMat τ b = toMat τ.rank B) (hB' : wordMat τ b.reverse = toMat τ.rank B')
    (hC : wordMat τ c = toMat τ.rank C) (hC' : wordMat τ c.reverse = toMat τ.rank C')
    (hD : wordMat τ d = toMat τ.rank D) (hD' : wordMat τ d.reverse = toMat τ.rank D') :
    wordMat τ (cw (cw a b) (cw c d)) = toMat τ.rank (ldc τ.rank A A' B B' C C' D D') := by
  have hab := wordMat_cw_eq hA hA' hB hB'
  have hba := wordMat_cw_eq hB hB' hA hA'
  have hcd := wordMat_cw_eq hC hC' hD hD'
  have hdc := wordMat_cw_eq hD hD' hC hC'
  rw [ldc]
  refine wordMat_cw_eq hab ?_ hcd ?_
  · rw [cw_reverse]
    exact hba
  · rw [cw_reverse]
    exact hdc

theorem wordMat_dc_inv_eq {a b c d : List (Fin τ.rank)} {A A' B B' C C' D D' : List (List ℤ)}
    (hA : wordMat τ a = toMat τ.rank A) (hA' : wordMat τ a.reverse = toMat τ.rank A')
    (hB : wordMat τ b = toMat τ.rank B) (hB' : wordMat τ b.reverse = toMat τ.rank B')
    (hC : wordMat τ c = toMat τ.rank C) (hC' : wordMat τ c.reverse = toMat τ.rank C')
    (hD : wordMat τ d = toMat τ.rank D) (hD' : wordMat τ d.reverse = toMat τ.rank D') :
    wordMat τ (cw (cw a b) (cw c d)).reverse =
      toMat τ.rank (ldcInv τ.rank A A' B B' C C' D D') := by
  have hab := wordMat_cw_eq hA hA' hB hB'
  have hba := wordMat_cw_eq hB hB' hA hA'
  have hcd := wordMat_cw_eq hC hC' hD hD'
  have hdc := wordMat_cw_eq hD hD' hC hC'
  rw [ldcInv, cw_reverse]
  refine wordMat_cw_eq hcd ?_ hab ?_
  · rw [cw_reverse]
    exact hdc
  · rw [cw_reverse]
    exact hba

theorem dc_eq_smul_pow {a b c d w : List (Fin τ.rank)}
    {A A' B B' C C' D D' W : List (List ℤ)} {s : ℤ} {k : ℕ}
    (hA : wordMat τ a = toMat τ.rank A) (hA' : wordMat τ a.reverse = toMat τ.rank A')
    (hB : wordMat τ b = toMat τ.rank B) (hB' : wordMat τ b.reverse = toMat τ.rank B')
    (hC : wordMat τ c = toMat τ.rank C) (hC' : wordMat τ c.reverse = toMat τ.rank C')
    (hD : wordMat τ d = toMat τ.rank D) (hD' : wordMat τ d.reverse = toMat τ.rank D')
    (hW : wordMat τ w = toMat τ.rank W)
    (h : ldc τ.rank A A' B B' C C' D D' = lsmul τ.rank s (lpow τ.rank W k)) :
    wordMat τ (cw (cw a b) (cw c d)) = s • wordMat τ w ^ k := by
  rw [wordMat_dc_eq hA hA' hB hB' hC hC' hD hD', hW, ← toMat_lpow, ← toMat_lsmul, h]

theorem comm_of_lists {a w : List (Fin τ.rank)} {A W : List (List ℤ)}
    (hA : wordMat τ a = toMat τ.rank A) (hW : wordMat τ w = toMat τ.rank W)
    (h : lmul τ.rank A W = lmul τ.rank W A) :
    wordMat τ a * wordMat τ w = wordMat τ w * wordMat τ a := by
  rw [hA, hW, ← toMat_lmul, ← toMat_lmul, h]

theorem cw_pow_of_lists {a b : List (Fin τ.rank)} {A A' B B' : List (List ℤ)} {k : ℕ}
    (hA : wordMat τ a = toMat τ.rank A) (hA' : wordMat τ a.reverse = toMat τ.rank A')
    (hB : wordMat τ b = toMat τ.rank B) (hB' : wordMat τ b.reverse = toMat τ.rank B')
    (h : lpow τ.rank (lcw τ.rank A A' B B') k = lid τ.rank) : wordMat τ (cw a b) ^ k = 1 := by
  rw [wordMat_cw_eq hA hA' hB hB', ← toMat_lpow, h, toMat_lid]

theorem cert_of_lists {X Y : List (List ℤ)} {N : ℤ}
    (h : lmul τ.rank (ladd τ.rank X (lsmul τ.rank (-1) (lid τ.rank))) Y =
      lsmul τ.rank N (lid τ.rank)) :
    (toMat τ.rank X - 1) * toMat τ.rank Y = N • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) := by
  have h1 := congrArg (toMat τ.rank) h
  simp only [toMat_lmul, toMat_ladd, toMat_lsmul, toMat_lid] at h1
  simpa [sub_eq_add_neg] using h1

theorem cert2_of_lists {X₁ Y₁ X₂ Y₂ : List (List ℤ)}
    (h : ladd τ.rank (lmul τ.rank (ladd τ.rank X₁ (lsmul τ.rank (-1) (lid τ.rank))) Y₁)
      (lmul τ.rank (ladd τ.rank X₂ (lsmul τ.rank (-1) (lid τ.rank))) Y₂) = lid τ.rank) :
    (toMat τ.rank X₁ - 1) * toMat τ.rank Y₁ + (toMat τ.rank X₂ - 1) * toMat τ.rank Y₂ = 1 := by
  have h1 := congrArg (toMat τ.rank) h
  simp only [toMat_lmul, toMat_ladd, toMat_lsmul, toMat_lid] at h1
  simpa [sub_eq_add_neg] using h1

end Words

section Fpf2

variable {L : Type} [Field L]

theorem zpowMatrix_add' (M N : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (t : Fin τ.rank → Lˣ) :
    zpowMatrix (M + N) t = zpowMatrix M t * zpowMatrix N t := by
  funext j
  simp only [zpowMatrix_apply, Matrix.add_apply, zpow_add, Finset.prod_mul_distrib, Pi.mul_apply]

theorem fpf2_of_matrix_cert {u₁ u₂ : WeylGroup τ} {Y₁ Y₂ : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hY : (weylMat u₁⁻¹ - 1) * Y₁ + (weylMat u₂⁻¹ - 1) * Y₂ = 1) {β : Fin τ.rank → Lˣ}
    (hβ₁ : weylTuple u₁ β = β) (hβ₂ : weylTuple u₂ β = β) : rootDiagUnit τ β = 1 := by
  rw [weylTuple_eq_zpowMatrix] at hβ₁ hβ₂
  have h1 : zpowMatrix (weylMat u₁⁻¹ - 1) β = 1 := by
    rw [zpowMatrix_sub, zpowMatrix_one, hβ₁, mul_inv_cancel]
  have h2 : zpowMatrix (weylMat u₂⁻¹ - 1) β = 1 := by
    rw [zpowMatrix_sub, zpowMatrix_one, hβ₂, mul_inv_cancel]
  have h3 : zpowMatrix ((weylMat u₁⁻¹ - 1) * Y₁ + (weylMat u₂⁻¹ - 1) * Y₂) β = 1 := by
    rw [zpowMatrix_add', ← zpowMatrix_zpowMatrix, ← zpowMatrix_zpowMatrix, h1, h2, map_one,
      map_one, mul_one]
  rw [hY, zpowMatrix_one] at h3
  rw [h3, rootDiagUnit_one]

end Fpf2

section Cert

theorem torusFpf_of_cert {q p : ℕ} {w u : WeylGroup τ}
    {Y : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {N : ℤ}
    (hY : (weylMat u⁻¹ - 1) * Y = N • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ))
    (hp : p.Prime) (hN : ¬ (p : ℤ) ∣ N) : TorusFpf τ q p w u := by
  intro L _ _ Fr _ β _ hβp hfix
  exact fpf_of_matrix_cert hY hp hN hβp hfix

theorem torusFpf2_of_cert {q p : ℕ} {w u₁ u₂ : WeylGroup τ}
    {Y₁ Y₂ : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hY : (weylMat u₁⁻¹ - 1) * Y₁ + (weylMat u₂⁻¹ - 1) * Y₂ = 1) : TorusFpf2 τ q p w u₁ u₂ := by
  intro L _ _ Fr _ β _ hβp hfix₁ hfix₂
  exact fpf2_of_matrix_cert hY hfix₁ hfix₂

theorem SylowFrame.wcOn_dcw_cert {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    {w a b c d : List (Fin τ.rank)} (hF : SylowFrame τ F p (wp τ w))
    (ha : wordMat τ a * wordMat τ w = wordMat τ w * wordMat τ a)
    (hb : wordMat τ b * wordMat τ w = wordMat τ w * wordMat τ b)
    (hc : wordMat τ c * wordMat τ w = wordMat τ w * wordMat τ c)
    (hd : wordMat τ d * wordMat τ w = wordMat τ w * wordMat τ d)
    {Y : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {N : ℤ}
    (hY : (wordMat τ (cw (cw a b) (cw c d)).reverse - 1) * Y =
      N • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ))
    (hN : ¬ (p : ℤ) ∣ N) : WCOn p (adjointGroup τ F) := by
  refine hF.wcOn_dc (wp_mem_centralizer ha) (wp_mem_centralizer hb) (wp_mem_centralizer hc)
    (wp_mem_centralizer hd) (torusFpf_of_cert (Y := Y) (N := N) ?_ Fact.out hN)
  rw [← wp_cw, ← wp_cw, ← wp_cw, weylMat_wp_inv]
  exact hY

theorem SylowFrame.wcOn_dcw2_cert {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    {w a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : List (Fin τ.rank)} (hF : SylowFrame τ F p (wp τ w))
    (ha₁ : wordMat τ a₁ * wordMat τ w = wordMat τ w * wordMat τ a₁)
    (hb₁ : wordMat τ b₁ * wordMat τ w = wordMat τ w * wordMat τ b₁)
    (hc₁ : wordMat τ c₁ * wordMat τ w = wordMat τ w * wordMat τ c₁)
    (hd₁ : wordMat τ d₁ * wordMat τ w = wordMat τ w * wordMat τ d₁)
    (ha₂ : wordMat τ a₂ * wordMat τ w = wordMat τ w * wordMat τ a₂)
    (hb₂ : wordMat τ b₂ * wordMat τ w = wordMat τ w * wordMat τ b₂)
    (hc₂ : wordMat τ c₂ * wordMat τ w = wordMat τ w * wordMat τ c₂)
    (hd₂ : wordMat τ d₂ * wordMat τ w = wordMat τ w * wordMat τ d₂)
    {Y₁ Y₂ : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hY : (wordMat τ (cw (cw a₁ b₁) (cw c₁ d₁)).reverse - 1) * Y₁ +
      (wordMat τ (cw (cw a₂ b₂) (cw c₂ d₂)).reverse - 1) * Y₂ = 1) :
    WCOn p (adjointGroup τ F) := by
  refine hF.wcOn_dc2 (wp_mem_centralizer ha₁) (wp_mem_centralizer hb₁) (wp_mem_centralizer hc₁)
    (wp_mem_centralizer hd₁) (wp_mem_centralizer ha₂) (wp_mem_centralizer hb₂)
    (wp_mem_centralizer hc₂) (wp_mem_centralizer hd₂) (torusFpf2_of_cert (Y₁ := Y₁) (Y₂ := Y₂) ?_)
  rw [← wp_cw, ← wp_cw, ← wp_cw, ← wp_cw, ← wp_cw, ← wp_cw, weylMat_wp_inv, weylMat_wp_inv]
  exact hY

end Cert

section Vec

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

theorem zpow_eq_of_dvd_sub {L : Type} [Field L] {ζ : Lˣ} {p : ℕ} (hζ : orderOf ζ = p) {a b : ℤ}
    (h : (p : ℤ) ∣ a - b) : ζ ^ a = ζ ^ b := by
  rw [← hζ] at h
  have h1 := orderOf_dvd_iff_zpow_eq_one.1 h
  rw [zpow_sub] at h1
  exact mul_inv_eq_one.1 h1

theorem WeakFrame.wcOn_noncomm_vec {w : WeylGroup τ} (hF : WeakFrame τ F w)
    (hpq : ¬ p ∣ Nat.card F) {X Y s : WeylGroup τ}
    (hX : X ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hY : Y ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hs : s ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ))) (hv : ⁅X, Y⁆ ^ p = 1) {q₀ : ℤ}
    (hq₀ : (Nat.card F : ℤ) ≡ q₀ [ZMOD p]) (vec : Fin τ.rank → ℤ)
    (hvec : ∀ j, (p : ℤ) ∣ q₀ * (∑ i, vec i * weylMat w⁻¹ i j) - vec j) (j : Fin τ.rank)
    (hj : ¬ (p : ℤ) ∣ ∑ i, vec i * ((weylMat s⁻¹ - 1) * (weylMat ⁅X, Y⁆⁻¹ - 1)) i j) :
    WCOn p (adjointGroup τ F) := by
  obtain ⟨L, _, _, Fr, D, hFr, hK0, hΦ, hn, ⟨e⟩⟩ := hF
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf_prime_of_not_dvd (L := L) Fact.out hpq hK0
  have hβq : weylTuple w (fun i => (ζ ^ vec i) ^ Nat.card F) = fun i => ζ ^ vec i := by
    rw [weylTuple_eq_zpowMatrix]
    funext j'
    rw [zpowMatrix_apply]
    have e1 : ∀ i, ((ζ ^ vec i) ^ Nat.card F) ^ weylMat w⁻¹ i j' =
        ζ ^ (vec i * (Nat.card F : ℤ) * weylMat w⁻¹ i j') := by
      intro i
      rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_assoc]
    simp only [e1]
    rw [Finset.prod_zpow_eq_zpow_sum]
    show _ = ζ ^ vec j'
    have e2 : ∑ i, vec i * (Nat.card F : ℤ) * weylMat w⁻¹ i j' =
        (Nat.card F : ℤ) * ∑ i, vec i * weylMat w⁻¹ i j' := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e2]
    refine zpow_eq_of_dvd_sub hζ ?_
    have h2 : (p : ℤ) ∣ q₀ - (Nat.card F : ℤ) := hq₀.dvd
    have h3 := dvd_sub (hvec j') (Dvd.dvd.mul_right h2 (∑ i, vec i * weylMat w⁻¹ i j'))
    have h4 : q₀ * (∑ i, vec i * weylMat w⁻¹ i j') - vec j' -
        (q₀ - (Nat.card F : ℤ)) * (∑ i, vec i * weylMat w⁻¹ i j') =
        (Nat.card F : ℤ) * (∑ i, vec i * weylMat w⁻¹ i j') - vec j' := by ring
    rwa [h4] at h3
  have hβT : rootDiagUnit τ (fun i => ζ ^ vec i) ∈ D.torus := by
    rw [torus_eq_twistedTorus D hΦ, hn]
    exact mem_twistedTorus_of_coord hFr hβq
  have hβp : rootDiagUnit τ (fun i => ζ ^ vec i) ^ p = 1 := by
    rw [rootDiagUnit_pow_eq]
    have : (fun i => (ζ ^ vec i) ^ p) = fun _ => (1 : Lˣ) := by
      funext i
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hζ, pow_orderOf_eq_one,
        one_zpow]
    rw [this]
    exact rootDiagUnit_one
  exact wcOn_noncomm_of_frame D hFr hΦ hn e hX hY hs hv hβT hβp
    (noncomm_coord hζ vec j s ⁅X, Y⁆ hj)

end Vec

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
