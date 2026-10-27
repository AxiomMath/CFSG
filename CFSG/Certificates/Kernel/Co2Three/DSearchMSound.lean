module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeKit
public import CFSG.RankThree.Native.F2Tail
public import CFSG.Certificates.Kernel.PackSetSound
public import Certificates.Data.Kernel.Co2Three.DSearchM

public section

namespace CFSG.KC.Co2Three

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.Native.F2 CFSG.KC.Enum CFSG.Certificates.ChainArrays
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T

theorem foldr_range_addN (g : ℕ → ℕ) : ∀ c a,
    (List.range c).foldr (fun k s => Nat.add s (g k)) a = a + ∑ k ∈ Finset.range c, g k
  | 0, a => by simp
  | c + 1, a => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_range_addN g c,
      Finset.sum_range_succ]
    change a + g c + _ = _
    omega

theorem foldN_addN_eq (g : ℕ → ℕ) (c : ℕ) :
    foldN c (fun k s => Nat.add s (g k)) 0 = ∑ k ∈ Finset.range c, g k := by
  rw [CFSG.KC.Pack.foldN_eq, foldr_range_addN, Nat.zero_add]

variable {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ}

theorem vg_vidx (hs : Sys d V VG LK) {w : ℕ} (hw : w ∈ V) : VG (vidx V w) = w := by
  obtain ⟨hlt, hget⟩ := getElem_vidx hw
  rw [← hs.vg _ hlt, hget]

theorem vg_apply {n : ℕ} (hs : Sys d V VG LK) (hn : V.size = n) {A : ℕ}
    (hA : ∀ v ∈ V, vmul d v A ∈ V) {σ : Equiv.Perm (Fin n)} (hσ : Rep n (permOfMat d V A) σ)
    (q : Fin n) : VG (σ q : ℕ) = vmul d (VG q) A := by
  have hq : (q : ℕ) < V.size := hn ▸ q.2
  rw [← hσ q, hs.perm_get hq, vg_vidx hs (hA _ (hs.mem hq))]

theorem rep_mmul {n : ℕ} (hn : V.size = n) {A T : ℕ} (hT : ∀ v ∈ V, vmul d v T ∈ V)
    {σ τ : Equiv.Perm (Fin n)} (hσ : Rep n (permOfMat d V A) σ) (hτ : Rep n (permOfMat d V T) τ) :
    Rep n (permOfMat d V (mmul d T A)) (σ * τ) := by
  rw [← compA_permOfMat hT, hn]
  exact rep_compA hσ hτ

@[expose] def Passes {n : ℕ} (Q : RawSchreierDatum n) (d : ℕ) (V : Array ℕ) (VG : ℕ → ℕ)
    (RF : ℕ → Bool) (RS RY : ℕ → ℕ) (FX : ℕ → ℕ → Bool) (PR : ℕ → Bool)
    (c : Equiv.Perm (Fin n)) : Prop :=
  (∀ l (hl : l < Q.baseCount), RF l = true → ∃ hs : RS l < l, ∃ Y : Equiv.Perm (Fin n),
    Rep n (permOfMat d V (RY l)) Y ∧
      c (Q.base.get ⟨l, hl⟩) = Y (c (Q.base.get ⟨RS l, by omega⟩))) ∧
  (∀ l (hl : l < Q.baseCount), FX l (VG (c (Q.base.get ⟨l, hl⟩))) = true) ∧
  (∀ A, (∀ v ∈ V, vmul d v A ∈ V) → Rep n (permOfMat d V A) c → PR A = true)

variable {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ} {vm mm : ℕ → ℕ → ℕ} {m : ℕ → ℕ} {PT PO TM TIM : ℕ → ℕ → ℕ}
  {BS : ℕ → ℕ} {RF FF : ℕ → Bool} {RS RY : ℕ → ℕ} {FX : ℕ → ℕ → Bool} {PR : ℕ → Bool}

theorem dsearchM_spec (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
    (hQ : ValidSchreier Q) (hs : Sys d V VG LK) (hn : V.size = n)
    (hvm : ∀ v M, vm v M = vmul d v M) (hmm : ∀ A B, mm A B = mmul d A B)
    (hL : LevFacts d V (rawLevels n S base) Q.baseCount m PT PO TM TIM)
    (hBS : ∀ i < Q.baseCount, base[i]! = BS i)
    (hRY : ∀ l < Q.baseCount, RF l = true → ∀ v ∈ V, vmul d v (RY l) ∈ V) :
    ∀ fuel i, i + fuel = Q.baseCount → ∀ (A AI : ℕ) (σ : Equiv.Perm (Fin n)),
      (∀ v ∈ V, vmul d v A ∈ V) → mmul d A AI = idM d → Rep n (permOfMat d V A) σ →
      ∀ K : Finset (Equiv.Perm (Fin n)),
        (∀ c ∈ K, σ⁻¹ * c ∈ Q.levelSubgroup i ∧ Passes Q d V VG RF RS RY FX PR c) →
        K.card ≤ dsearchM vm mm VG BS LK RF FF RS RY FX PR m PT PO TM TIM fuel i A AI := by
  have hbase : ∀ l (hl : l < Q.baseCount), ((Q.base.get ⟨l, hl⟩ : Fin n) : ℕ) = BS l :=
    fun l hl => (hA.base_val ⟨l, hl⟩).trans (hBS l hl)
  intro fuel
  induction fuel with
  | zero =>
    intro i hi A AI σ hAm _ hσ K hK
    rw [Nat.add_zero] at hi
    subst hi
    have hKσ : ∀ c ∈ K, c = σ := by
      intro c hc
      have h := (hK c hc).1
      rw [Q.levelSubgroup_terminal_eq_bot hQ, Subgroup.mem_bot, inv_mul_eq_one] at h
      exact h.symm
    rcases K.eq_empty_or_nonempty with he | ⟨c, hc⟩
    · rw [he, Finset.card_empty]
      exact Nat.zero_le _
    · have hp : PR A = true := (hK c hc).2.2.2 A hAm (hKσ c hc ▸ hσ)
      rw [dsearchM, hp]
      exact Finset.card_le_one.2 fun a ha b hb => (hKσ a ha).trans (hKσ b hb).symm
  | succ fuel ih =>
    intro i hi A AI σ hAm hAI hσ K hK
    have hib : i < Q.baseCount := by omega
    have hsz : (lev n S base i).pts.size = m i := hL.pts_size i hib
    have child : ∀ k < m i, ∀ K' : Finset (Equiv.Perm (Fin n)),
        (∀ c ∈ K', (levT n S base i k)⁻¹ * (σ⁻¹ * c) ∈ Q.levelSubgroup (i + 1) ∧
          Passes Q d V VG RF RS RY FX PR c) →
        K'.card ≤ dsearchM vm mm VG BS LK RF FF RS RY FX PR m PT PO TM TIM fuel (i + 1)
          (mm (TM i k) A) (mm AI (TIM i k)) := by
      intro k hk K' hK'
      have hinv := hL.inv i hib k hk
      have hT : Rep n (permOfMat d V (TM i k)) (levT n S base i k) := by
        rw [← hL.tr i hib k hk]
        exact hA.rep_levT hF hib (by rw [hsz]; exact hk)
      rw [hmm, hmm]
      refine ih (i + 1) (by omega) _ _ (σ * levT n S base i k) (maps_mmul hinv.1 hAm)
        (mmul_inv_cancel hs.hd hinv.2.2.1 hAI) (rep_mmul hn hinv.1 hσ hT) K' fun c hc => ?_
      refine ⟨?_, (hK' c hc).2⟩
      rw [mul_inv_rev, mul_assoc]
      exact (hK' c hc).1
    set b := Q.base.get ⟨i, hib⟩ with hbdef
    set key : Equiv.Perm (Fin n) → ℕ := fun c => (lev n S base i).pos[(((σ⁻¹ * c) b : Fin n) : ℕ)]!
      with hkeydef
    have hkey : ∀ c ∈ K, key c < m i ∧
        (levT n S base i (key c))⁻¹ * (σ⁻¹ * c) ∈ Q.levelSubgroup (i + 1) := by
      intro c hc
      have h := levT_pos_inv_mul_mem hA hF hQ hib (hK c hc).1
      rw [hsz] at h
      exact h
    have hpt : ∀ c ∈ K, PT i (key c) = ((σ⁻¹ * c) b : ℕ) := by
      intro c hc
      rw [← hL.pts i hib _ (hkey c hc).1]
      exact (hA.levelFacts hF hib).pts_pos _ ((σ⁻¹ * c) b).2 (by rw [hsz]; exact (hkey c hc).1)
    have hvc : ∀ c : Equiv.Perm (Fin n), VG (c b : ℕ) = vmul d (VG ((σ⁻¹ * c) b : ℕ)) A := by
      intro c
      have e : c b = σ ((σ⁻¹ * c) b) := by simp
      rw [e, vg_apply hs hn hAm hσ]
    rw [dsearchM]
    cases hr : RF i with
    | false =>
      change K.card ≤ foldN (m i) _ 0
      simp only [CFSG.KC.Pack.strictN_eq]
      rw [foldN_addN_eq, Finset.card_eq_sum_card_fiberwise (f := key) (t := Finset.range (m i))
        (by intro c hc; exact Finset.mem_range.2 (hkey c hc).1)]
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_range] at hk
      beta_reduce
      rcases (K.filter fun c => key c = k).eq_empty_or_nonempty with he | ⟨c0, hc0⟩
      · rw [he, Finset.card_empty]
        exact Nat.zero_le _
      · rw [Finset.mem_filter] at hc0
        obtain ⟨hc0K, hc0k⟩ := hc0
        have htest : bIf(FF i, FX i (vm (VG (PT i k)) A), true) = true := by
          cases FF i
          · rfl
          · change FX i (vm (VG (PT i k)) A) = true
            rw [← hc0k, hpt c0 hc0K, hvm, ← hvc]
            exact (hK c0 hc0K).2.2.1 i hib
        rw [htest]
        refine child k hk _ fun c hc => ?_
        rw [Finset.mem_filter] at hc
        refine ⟨?_, (hK c hc.1).2⟩
        rw [← hc.2]
        exact (hkey c hc.1).2
    | true =>
      change K.card ≤ strictN (vm (vm (VG (BS (RS i))) A) (RY i)) _
      simp only [CFSG.KC.Pack.strictN_eq]
      rcases K.eq_empty_or_nonempty with he | ⟨c0, hc0⟩
      · rw [he, Finset.card_empty]
        exact Nat.zero_le _
      have hu : ∀ c ∈ K, vm (vm (VG (BS (RS i))) A) (RY i) = VG (c b : ℕ) := by
        intro c hc
        obtain ⟨hsl, Y, hY, hcY⟩ := (hK c hc).2.1 i hib hr
        have hfix : (σ⁻¹ * c) (Q.base.get ⟨RS i, by omega⟩) = Q.base.get ⟨RS i, by omega⟩ :=
          Q.levelSubgroup_fixes_base_index i _ (hK c hc).1 ⟨RS i, by omega⟩ hsl
        have hcs : c (Q.base.get ⟨RS i, by omega⟩) = σ (Q.base.get ⟨RS i, by omega⟩) :=
          calc c (Q.base.get ⟨RS i, by omega⟩)
              = σ ((σ⁻¹ * c) (Q.base.get ⟨RS i, by omega⟩)) := by simp
            _ = σ (Q.base.get ⟨RS i, by omega⟩) := by rw [hfix]
        rw [hcY, vg_apply hs hn (hRY i hib hr) hY, hcs, vg_apply hs hn hAm hσ,
          hbase (RS i) (by omega), hvm, hvm]
      have hk : ∀ c ∈ K, PO i (LK (vm (vm (vm (VG (BS (RS i))) A) (RY i)) AI)) = key c := by
        intro c hc
        have hq : (((σ⁻¹ * c) b : Fin n) : ℕ) < V.size := by
          rw [hn]
          exact ((σ⁻¹ * c) b).2
        rw [hu c hc, hvc c, hvm, ← vmul_mmul, hAI, vmul_idM hs.hd (hs.lt _ (hs.mem hq)),
          hs.lk _ hq, hkeydef]
        exact (hL.pos i hib _ hq).symm
      have hfx : FX i (vm (vm (VG (BS (RS i))) A) (RY i)) = true := by
        rw [hu c0 hc0]
        exact (hK c0 hc0).2.2.1 i hib
      have hlt : Nat.blt (key c0) (m i) = true := by
        rw [Nat.blt_eq]
        exact (hkey c0 hc0).1
      rw [hfx, hk c0 hc0, hlt]
      refine child (key c0) (hkey c0 hc0).1 K fun c hc => ⟨?_, (hK c hc).2⟩
      rw [(hk c0 hc0).symm.trans (hk c hc)]
      exact (hkey c hc).2

theorem card_le_dsearchM (hA : ChainArrays Q O S base W)
    (hF : ChainCheckFacts n O S base W chunks) (hQ : ValidSchreier Q) (hs : Sys d V VG LK)
    (hn : V.size = n) (hvm : ∀ v M, vm v M = vmul d v M) (hmm : ∀ A B, mm A B = mmul d A B)
    {nb : ℕ} (hnb : Q.baseCount = nb) (hL : LevFacts d V (rawLevels n S base) nb m PT PO TM TIM)
    (hBS : ∀ i < nb, base[i]! = BS i)
    (hRY : ∀ l < nb, RF l = true → ∀ v ∈ V, vmul d v (RY l) ∈ V) {I : ℕ} (hI : I = idM d)
    {X : Set (Equiv.Perm (Fin n))} (hX : ∀ c ∈ X, c ∈ Q.originalSubgroup)
    (hrel : ∀ c ∈ X, ∀ l (hl : l < Q.baseCount), RF l = true → ∃ hs : RS l < l,
      ∃ Y : Equiv.Perm (Fin n), Rep n (permOfMat d V (RY l)) Y ∧
        c (Q.base.get ⟨l, hl⟩) = Y (c (Q.base.get ⟨RS l, by omega⟩)))
    (hfix : ∀ c ∈ X, ∀ l (hl : l < Q.baseCount), FX l (VG (c (Q.base.get ⟨l, hl⟩))) = true)
    (hpred : ∀ c ∈ X, ∀ A, (∀ v ∈ V, vmul d v A ∈ V) → Rep n (permOfMat d V A) c →
      PR A = true) :
    Nat.card X ≤ dsearchM vm mm VG BS LK RF FF RS RY FX PR m PT PO TM TIM nb 0 I I := by
  subst hnb hI
  rw [Nat.card_eq_card_finite_toFinset (Set.toFinite X)]
  have hid : Rep n (permOfMat d V (idM d)) 1 := by
    rw [permOfMat_idM hs.hd hs.nodup hs.lt, hn]
    exact rep_idA
  refine dsearchM_spec hA hF hQ hs hn hvm hmm hL hBS hRY Q.baseCount 0 (by omega) _ _ 1
    (fun v hv => by rw [vmul_idM hs.hd (hs.lt v hv)]; exact hv) (mmul_idM_idM hs.hd) hid _
    fun c hc => ?_
  rw [Set.Finite.mem_toFinset] at hc
  refine ⟨?_, hrel c hc, hfix c hc, hpred c hc⟩
  rw [inv_one, one_mul, Q.levelSubgroup_zero_eq_original hQ]
  exact hX c hc

end CFSG.KC.Co2Three

end
