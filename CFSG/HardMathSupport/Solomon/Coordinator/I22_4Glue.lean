module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Bar
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Omega
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns

theorem i224_le_gammaPrimeIn {G : Type*} [Group G] [Finite G] {p k : ℕ} {B X E : Subgroup G}
    (hEB : E ≤ B) (hk : k ≤ CFSG.Open.pRank p E) :
    X ⊓ Subgroup.centralizer (E : Set G) ≤ gammaPrimeIn p k B X := by
  unfold gammaPrimeIn
  exact le_iSup₂_of_le (f := fun (E : Subgroup G) (_ : E ≤ B ∧ k ≤ CFSG.Open.pRank p E) =>
    X ⊓ Subgroup.centralizer (E : Set G)) E ⟨hEB, hk⟩ le_rfl

theorem input22_4_general {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X B L : Subgroup G} (hBX : B ≤ X) (hB : IsElemAbelian p B) (hL : GLAPComponent p X L)
    (hrank : 1 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.normalizer (L : Set G)))
    (hgen : L ≤ gammaPrimeIn p (CFSG.Open.pRank p (B ⊓ Subgroup.normalizer (L : Set G)) - 1)
      (B ⊓ Subgroup.normalizer (L : Set G)) L) :
    IsInGMinusOne p B L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hLX : L ≤ X := hL.1
  set A : Subgroup G := B ⊓ Subgroup.normalizer (L : Set G) with hA
  have hAB : A ≤ B := inf_le_left
  have hAel : IsElemAbelian p A := isElemAbelian_of_le' hB hAB
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian' hB
  have hAp : IsPGroup p A := isPGroup_of_isElemAbelian' hAel
  have hA'eq := i224_barX_inf_normalizer (B := B) hL
  have hcardA : Nat.card (barX p X A) = Nat.card A := i224_card_barX hp hAp (hAB.trans hBX)
  have hcardB : Nat.card (barX p X B) = Nat.card B := i224_card_barX hp hBp hBX
  have hctx : I224Ctx p (barX p X B) (barX p X L) :=
    { prime := hp
      elem := isElemAbelian_barX hB
      quasi := hL.2.2.1.2.2
      dist := fun g _ g' _ hne => i224_comm_cj hL.2.2.1 g g' hne
      gen := by
        rw [hA'eq]
        refine barX_le_of_pre ?_
        unfold gammaPrimeIn at hgen
        refine hgen.trans (iSup₂_le fun E hE x hx => ?_)
        refine mem_i224Pre.2 ⟨hLX hx.1, ?_⟩
        have hEA := hE.1
        have hEel : IsElemAbelian p E := isElemAbelian_of_le' hAel hEA
        have hEX : E ≤ X := hEA.trans (hAB.trans hBX)
        have hF : barX p X E ≤ barX p X A ∧
            Nat.card (barX p X A) ≤ p * Nat.card (barX p X E) := by
          refine ⟨barX_mono p hEA, ?_⟩
          rw [hcardA, i224_card_barX hp (isPGroup_of_isElemAbelian' hEel) hEX]
          exact (i224_card_le_iff hp hAel hEel).1 hE.2
        refine Subgroup.mem_iSup_of_mem (barX p X E) (Subgroup.mem_iSup_of_mem hF ⟨?_, ?_⟩)
        · exact ⟨⟨x, hLX hx.1⟩, (Subgroup.mem_subgroupOf).2 hx.1, rfl⟩
        · refine Subgroup.mem_centralizer_iff.2 ?_
          rintro _ ⟨e, he, rfl⟩
          have := Subgroup.mem_centralizer_iff.1 hx.2 (e : G) ((Subgroup.mem_subgroupOf).1 he)
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext this }
  have hΩ := i224_omega hctx
  set K : Subgroup G := bClosure B L with hK
  have hKX : K ≤ X := by
    refine iSup₂_le fun b hb => ?_
    have hX : GLBConj b X = X := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hBX hb))
    exact (gLBConj_mono b hLX).trans hX.le
  have hKconj : ∀ b ∈ B, ∀ x ∈ K, b * x * b⁻¹ ∈ K := by
    intro b hb
    have key : K ≤ K.comap (MulAut.conj b).toMonoidHom := by
      refine iSup₂_le fun g hg y hy => ?_
      show b * y * b⁻¹ ∈ K
      have h1 : b * y * b⁻¹ ∈ GLBConj (g * b⁻¹) L := by
        rw [mem_gLBConj]
        have := mem_gLBConj.1 hy
        have e : g * b⁻¹ * (b * y * b⁻¹) * (g * b⁻¹)⁻¹ = g * y * g⁻¹ := by group
        rw [e]
        exact this
      exact Subgroup.mem_iSup_of_mem (g * b⁻¹)
        (Subgroup.mem_iSup_of_mem (B.mul_mem hg (B.inv_mem hb)) h1)
    intro x hx
    exact key hx
  have hBK : ∀ b ∈ B, b ∈ Subgroup.normalizer (K : Set G) := fun b hb => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hKconj b hb x, fun h => ?_⟩
    have := hKconj b⁻¹ (B.inv_mem hb) _ h
    have e : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x := by group
    rw [e] at this
    exact this
  have hKpre : K ≤ i224Pre p X (i224K (barX p X B) (barX p X L)) := by
    refine iSup₂_le fun b hb x hx => ?_
    have hbX := hBX hb
    have hxX : x ∈ X := ((gLBConj_mono b hLX).trans
      (gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hbX)).le) hx
    refine mem_i224Pre.2 ⟨hxX, ?_⟩
    have hbB' : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨b, hbX⟩ ∈ barX p X B :=
      ⟨⟨b, hbX⟩, (Subgroup.mem_subgroupOf).2 hb, rfl⟩
    have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨b, hbX⟩ *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hxX⟩ *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨b, hbX⟩)⁻¹ ∈ barX p X L := by
      have hxL := mem_gLBConj.1 hx
      refine ⟨⟨b * x * b⁻¹, X.mul_mem (X.mul_mem hbX hxX) (X.inv_mem hbX)⟩,
        (Subgroup.mem_subgroupOf).2 hxL, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem
      ((barX p X B).inv_mem hbB') (mem_i224Cj.2 (by simpa using hmem)))
  have hKbar : i224K (barX p X B) (barX p X L) ≤ barX p X K := by
    refine iSup₂_le fun g hg z hz => ?_
    obtain ⟨b, hb, rfl⟩ := hg
    have hbB : (b : G) ∈ B := (Subgroup.mem_subgroupOf).1 hb
    obtain ⟨l, hl, hlz⟩ := mem_i224Cj.1 hz
    have hlL : (l : G) ∈ L := (Subgroup.mem_subgroupOf).1 hl
    have hmemK : (b : G) * l * (b : G)⁻¹ ∈ K := by
      have : (b : G) * l * (b : G)⁻¹ ∈ GLBConj (b : G)⁻¹ L := by
        rw [mem_gLBConj]
        have e : (b : G)⁻¹ * ((b : G) * l * (b : G)⁻¹) * (b : G)⁻¹⁻¹ = l := by group
        rw [e]
        exact hlL
      exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem (B.inv_mem hbB) this)
    refine ⟨b * l * b⁻¹, (Subgroup.mem_subgroupOf).2 hmemK, ?_⟩
    rw [map_mul, map_mul, map_inv, hlz]
    group
  set M : Subgroup G := gammaPrimeIn p (CFSG.Open.pRank p B - 1) B K with hM
  have hMK : M ≤ K := by
    rw [hM]
    unfold gammaPrimeIn
    exact iSup₂_le fun E _ => inf_le_left
  have hlift : ∀ E' : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X), E' ≤ barX p X B →
      Nat.card (barX p X B) ≤ p * Nat.card E' →
      i224K (barX p X B) (barX p X L) ⊓ Subgroup.centralizer (E' : Set _) ≤ barX p X M := by
    intro E' hE'B hcardE' z hz
    obtain ⟨hzK', hzC⟩ := hz
    set E : Subgroup G := B ⊓ i224Pre p X E' with hE
    have hEB : E ≤ B := inf_le_left
    have hEX : E ≤ X := hEB.trans hBX
    have hEel : IsElemAbelian p E := isElemAbelian_of_le' hB hEB
    have hEp : IsPGroup p E := isPGroup_of_isElemAbelian' hEel
    have hbarE : barX p X E = E' := by
      apply le_antisymm
      · rintro _ ⟨e, he, rfl⟩
        have he' := (Subgroup.mem_subgroupOf).1 he
        obtain ⟨hx, hT⟩ := mem_i224Pre.1 he'.2
        exact hT
      · intro y hy
        obtain ⟨b, hb, rfl⟩ := hE'B hy
        exact ⟨b, (Subgroup.mem_subgroupOf).2
          ⟨(Subgroup.mem_subgroupOf).1 hb, mem_i224Pre.2 ⟨b.2, hy⟩⟩, rfl⟩
    have hcardE : Nat.card E = Nat.card E' := by
      have := i224_card_barX hp hEp hEX
      rw [hbarE] at this
      exact this.symm
    have hrk : CFSG.Open.pRank p B - 1 ≤ CFSG.Open.pRank p E :=
      (i224_card_le_iff hp hB hEel).2 (by rw [← hcardB, hcardE]; exact hcardE')
    obtain ⟨k, hk, hkz⟩ := hKbar hzK'
    have hkK : (k : G) ∈ K := (Subgroup.mem_subgroupOf).1 hk
    have hVp : ¬ p ∣ Nat.card ↥(GLAPPrimeCoreOf p X ⊓ K) := fun h =>
      not_dvd_card_glaPPrimeCoreOf hp X (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hNX : ∀ x ∈ X, x ∈ Subgroup.normalizer (GLAPPrimeCoreOf p X : Set G) := fun x hx =>
      le_normalizer_glaPPrimeCoreOf p X hx
    have hx : ∀ u ∈ E, u * (k : G) * u⁻¹ * (k : G)⁻¹ ∈ GLAPPrimeCoreOf p X ⊓ K := by
      intro u hu
      have huX : u ∈ X := hEX hu
      obtain ⟨hux, huT⟩ := mem_i224Pre.1 (Subgroup.mem_inf.1 hu).2
      have hcomm := Subgroup.mem_centralizer_iff.1 hzC _ huT
      have h1 : (⟨u, huX⟩ : ↥X) * k * (⟨u, huX⟩ : ↥X)⁻¹ * k⁻¹ ∈ GLAPPrimeCore p ↥X := by
        refine (QuotientGroup.eq_one_iff _).1 ?_
        show QuotientGroup.mk' (GLAPPrimeCore p ↥X)
          ((⟨u, huX⟩ : ↥X) * k * (⟨u, huX⟩ : ↥X)⁻¹ * k⁻¹) = 1
        simp only [map_mul, map_inv]
        rw [hkz, hcomm]
        group
      exact ⟨⟨_, h1, rfl⟩, K.mul_mem
        ((Subgroup.mem_normalizer_iff.1 (hBK u (hEB hu)) _).1 hkK) (K.inv_mem hkK)⟩
    obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' (p := p) (U := E)
      (V := GLAPPrimeCoreOf p X ⊓ K) hEp hVp
      (fun e he => mem_normalizer_inf (hNX e (hEX he)) (hBK e (hEB he)))
      (x := (k : G)) (mem_normalizer_inf (hNX k k.2) (Subgroup.le_normalizer hkK)) hx
    have hk₁K : (k : G) * v ∈ K := K.mul_mem hkK hv.2
    have hk₁X : (k : G) * v ∈ X := hKX hk₁K
    have hk₁C : (k : G) * v ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := hfix u hu
      calc u * ((k : G) * v) = (u * ((k : G) * v) * u⁻¹) * u := by group
        _ = ((k : G) * v) * u := by rw [this]
    have hkπ : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨(k : G) * v, hk₁X⟩ = z := by
      have hvN : (⟨v, hKX hv.2⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := by
        obtain ⟨v', hv', hv'v⟩ := hv.1
        have : v' = ⟨v, hKX hv.2⟩ := Subtype.ext hv'v
        exact this ▸ hv'
      have hv1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨v, hKX hv.2⟩ : ↥X) = 1 :=
        (QuotientGroup.eq_one_iff _).2 hvN
      have e : (⟨(k : G) * v, hk₁X⟩ : ↥X) = k * ⟨v, hKX hv.2⟩ := rfl
      rw [e, map_mul, hv1, mul_one, hkz]
    have hz' : z ∈ barX p X (K ⊓ Subgroup.centralizer (E : Set G)) :=
      ⟨⟨(k : G) * v, hk₁X⟩, (Subgroup.mem_subgroupOf).2 ⟨hk₁K, hk₁C⟩, hkπ⟩
    exact barX_mono p (i224_le_gammaPrimeIn hEB hrk) hz'
  have hWle : i224W p (barX p X B) (i224K (barX p X B) (barX p X L)) ≤ barX p X M := by
    refine iSup₂_le fun E' hE' => ?_
    exact hlift E' hE'.1 hE'.2
  have hbarKM : barX p X K ≤ barX p X M := (barX_le_of_pre hKpre).trans (hΩ.trans hWle)
  have hNM : K ⊓ GLAPPrimeCoreOf p X ≤ M := by
    have hBnt : Nontrivial ↥B := by
      obtain ⟨a, ha⟩ := exists_card_eq_pow hp hAel
      have h1 : 1 ≤ a := by
        rw [← i224_pRank_eq hp hAel ha]
        exact hrank
      have h2 : 1 < Nat.card A := by
        rw [ha]
        exact Nat.one_lt_pow (by omega) hp.one_lt
      exact Finite.one_lt_card_iff_nontrivial.1 (lt_of_lt_of_le h2 (Subgroup.card_le_of_le hAB))
    have hEY : B ≤ Subgroup.normalizer ((K ⊓ GLAPPrimeCoreOf p X : Subgroup G) : Set G) :=
      fun b hb => mem_normalizer_inf (hBK b hb) (le_normalizer_glaPPrimeCoreOf p X (hBX hb))
    have hYp : ¬ p ∣ Nat.card ↥(K ⊓ GLAPPrimeCoreOf p X) := fun h =>
      not_dvd_card_glaPPrimeCoreOf hp X (h.trans (Subgroup.card_dvd_of_le inf_le_right))
    have hY := le_iSup_inf_centralizer_hyperplane (p := p) (E := B)
      (Y := K ⊓ GLAPPrimeCoreOf p X) hB hEY hYp
    refine hY.trans (iSup₂_le fun H hH => ?_)
    have hHB := hH.1
    have hHel : IsElemAbelian p H := isElemAbelian_of_le' hB hHB
    have hcard : Nat.card B ≤ p * Nat.card H := by
      have h1 := Subgroup.card_mul_index (H.subgroupOf B)
      rw [hH.2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHB).toEquiv] at h1
      rw [← h1, mul_comm]
    have hrk := (i224_card_le_iff hp hB hHel).2 hcard
    exact (inf_le_inf_right _ inf_le_left).trans (i224_le_gammaPrimeIn hHB hrk)
  have hKM : K ≤ M := by
    intro k hk
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le hbarKM hk (hKX hk)
    have h1 : j⁻¹ * k ∈ M := hNM ⟨K.mul_mem (K.inv_mem (hMK hj)) hk, hjk⟩
    have e : k = j * (j⁻¹ * k) := by group
    rw [e]
    exact M.mul_mem hj h1
  exact le_antisymm hKM hMK

theorem input22_4_holds : LocalBalance.Lemma54Ns.Input22_4 := by
  intro G _ _ X B L hBX hB hL hrank hgen
  exact input22_4_general Nat.prime_three hBX hB hL hrank hgen

end CFSG.HardMathSupport.Solomon.Coordinator
