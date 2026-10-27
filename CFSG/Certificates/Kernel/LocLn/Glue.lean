module

public import CFSG.Certificates.Kernel.LocLn.Sound
public import CFSG.Certificates.Kernel.LocLn.CoverSound
public import CFSG.Certificates.Kernel.ArrBfsCert
import CFSG.Certificates.Kernel.PackSetSound
import CFSG.Certificates.Kernel.U43Pk.Sound

public section

namespace CFSG.KS.LocLn

open CFSG.KD.LocLn CFSG.KC.Enum CFSG.KS.ArrBfsSim CFSG.Monster.B.Fischer
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc

theorem covN_spec {K : Kit} {N NR : ℕ} {T RX RT : ℕ → ℕ} {c X Y : ℕ}
    (h : covN K N NR T RX RT c X Y = true) :
    (c - 1) / N < NR ∧ eqN K (conjN K (T ((c - 1) % N)) (RX ((c - 1) / N))) X = true ∧
      eqN K (conjN K (T ((c - 1) % N)) (RT ((c - 1) / N))) Y = true := by
  unfold covN at h
  obtain ⟨-, h⟩ := CFSG.KC.Pack.band_iff.1 h
  simp only [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h2, h3⟩ := CFSG.KC.Pack.band_iff.1 h
  exact ⟨Nat.blt_eq.mp h1, h2, h3⟩

theorem blk_all {g : ℕ → Bool} {L Q : ℕ} (hL : 0 < L)
    (hb : ∀ q < Q, allBlk (Nat.mul L q) (fun i => strictB i g) L = true) :
    ∀ i < L * Q, g i = true := by
  intro i hi
  have h := CFSG.KC.Pack.allBlk_spec (hb (i / L) (Nat.div_lt_of_lt_mul hi)) (i % L)
    (Nat.mod_lt _ hL)
  simp only [CFSG.KC.Pack.strictB_eq] at h
  have e : Nat.add (Nat.mul L (i / L)) (i % L) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    exact Nat.div_add_mod i L
  rwa [e] at h

theorem mem_filter_map {N n8 : ℕ} {p : ℕ → Bool} {O : ℕ → ℕ}
    (h : (List.range N).filter p = (List.range n8).map O) {i : ℕ} (hi : i < N) (hp : p i = true) :
    ∃ a < n8, O a = i := by
  have hm : i ∈ (List.range N).filter p := List.mem_filter.2 ⟨List.mem_range.2 hi, hp⟩
  rw [h] at hm
  obtain ⟨a, ha, e⟩ := List.mem_map.1 hm
  exact ⟨a, List.mem_range.1 ha, e⟩

theorem locCheck_of {K : Kit} (hK : kitOK K = true) {n : ℕ} (hn : K.n = n)
    {inF : Array ℕ → Bool} {d : LocData} {m N NR n8 n2 : ℕ}
    {G T F O8 O2 CV RX RT PA LA SO SOI : ℕ → ℕ} {E : ℕ → ℕ → ℕ}
    (hgs : d.gens.size = m)
    (hG : ∀ k < m, codeN K d.gens[k]! (G k) = true ∧ validN K (G k) = true)
    (hN : 2 ≤ N) (hpt : ∀ i < N, ptN K m N G T E PA LA SO SOI i = true)
    (hfuel : N ≤ d.fuel) (hk : N = 2 ^ d.k)
    (hfl : ∀ i < N, flagN K (T i) = F i)
    (ho8 : (List.range N).filter (fun i => Nat.beq (F i % 2) 1) = (List.range n8).map O8)
    (ho2 : (List.range N).filter (fun i => Nat.beq (F i / 2) 1) = (List.range n2).map O2)
    (hpr : ∀ a < n8, pairN K N NR T O8 O2 CV RX RT n2 a = true)
    (hrs : d.reps.size = NR)
    (hrp : ∀ i < NR, codeN K d.reps[i]!.x (RX i) = true ∧ codeN K d.reps[i]!.t (RT i) = true ∧
      codeN K d.reps[i]!.g₁ (pkL d.reps[i]!.g₁.toList) = true ∧
      codeN K d.reps[i]!.g₂ (pkL d.reps[i]!.g₂.toList) = true ∧
      repN K (RX i) (RT i) (pkL d.reps[i]!.g₁.toList) (pkL d.reps[i]!.g₂.toList) d.reps[i]!.wa
        d.reps[i]!.wb d.reps[i]!.ma d.reps[i]!.mb d.reps[i]!.j = true)
    (hinF : ∀ i < NR, inF d.reps[i]!.g₁ = true ∧ inF d.reps[i]!.g₂ = true) :
    locCheck n inF d = true := by
  have Fk := kitF hK
  have hn0 : 0 < n := hn ▸ Fk.pos
  have hG' : ∀ k < m, d.gens[k]! = dec n (G k) ∧ validN K (G k) = true := fun k hk =>
    ⟨codeN_sound hn (hG k hk).1, (hG k hk).2⟩
  obtain ⟨Tb, hv, h0⟩ := tables_of hK hn hN hG' hpt
  have hc : ∀ i < N, Cd K (T i) := fun i hi => (valid_dec hK hn (ptN_spec (hpt i hi)).1).2
  have hbfs : locBfs n d = cert m N (fun i => dec n (T i)) E PA LA := by
    unfold locBfs
    rw [hgs, ← h0]
    exact arrBfs_eq Tb hfuel
  have hget : ∀ i < N, (cert m N (fun i => dec n (T i)) E PA LA).pts[i]! = dec n (T i) :=
    fun i hi => cert_pts_get hi
  have hrep : ∀ i < NR, repOK n inF d.reps[i]! = true ∧ d.reps[i]!.x = dec n (RX i) ∧
      d.reps[i]!.t = dec n (RT i) ∧ Cd K (RX i) ∧ Cd K (RT i) := by
    intro i hi
    obtain ⟨r1, r2, r3, r4, r5⟩ := hrp i hi
    have h5 := r5
    unfold repN at h5
    obtain ⟨v1, h5⟩ := CFSG.KC.Pack.band_iff.1 h5
    obtain ⟨v2, -⟩ := CFSG.KC.Pack.band_iff.1 h5
    exact ⟨repN_sound hK hn (codeN_sound hn r1) (codeN_sound hn r2) (codeN_sound hn r3)
      (codeN_sound hn r4) r5 (hinF i hi).1 (hinF i hi).2, codeN_sound hn r1, codeN_sound hn r2,
      (valid_dec hK hn v1).2, (valid_dec hK hn v2).2⟩
  have hcov : locCover n (cert m N (fun i => dec n (T i)) E PA LA).pts d.reps = true := by
    apply locCover_of hn0
    · intro i hi j hj e
      rw [cert_pts_size] at hi hj
      rw [hget i hi, hget j hj] at e
      exact Tb.key i hi j hj e
    · intro i hi
      rw [cert_pts_size] at hi
      rw [hget i hi]
      exact hv i hi
    · intro r hr
      rw [hrs] at hr
      exact repOK_valid (hrep r hr).1
    · intro i hi j hj h8 h2 hcm
      rw [cert_pts_size] at hi hj
      rw [hget i hi] at h8 hcm ⊢
      rw [hget j hj] at h2 hcm ⊢
      have fi := hfl i hi
      have fj := hfl j hj
      rw [flag_dec hK hn (hc i hi), h8] at fi
      rw [flag_dec hK hn (hc j hj), h2] at fj
      have p8 : Nat.beq (F i % 2) 1 = true := by
        rw [← fi, if_pos rfl]
        by_cases hc : isO2 n (dec n (T i)) = true
        · rw [if_pos hc]
          rfl
        · rw [if_neg hc]
          rfl
      have p2 : Nat.beq (F j / 2) 1 = true := by
        rw [← fj, if_pos rfl]
        by_cases hc : isO8 n (dec n (T j)) = true
        · rw [if_pos hc]
          rfl
        · rw [if_neg hc]
          rfl
      obtain ⟨a, ha, rfl⟩ := mem_filter_map ho8 hi p8
      obtain ⟨b, hb, rfl⟩ := mem_filter_map ho2 hj p2
      have hrow := hpr a ha
      unfold pairN at hrow
      rw [CFSG.KC.Pack.strictB_eq] at hrow
      have e := CFSG.KC.Pack.allBlk_spec hrow b hb
      rw [Nat.add_eq, Nat.zero_add, CFSG.KC.Pack.strictB_eq, CFSG.KS.U43Pk.bIf_eq,
        ← comm_dec hK hn (hc _ hi) (hc _ hj), hcm, if_pos rfl] at e
      obtain ⟨e1, e2, e3⟩ := covN_spec e
      set c := CV (Nat.add (Nat.mul n2 a) b)
      have hsi : (c - 1) % N < N := Nat.mod_lt _ (by omega)
      have hri : (c - 1) / N < d.reps.size := by rw [hrs]; exact e1
      obtain ⟨-, hx, ht, cx, ct⟩ := hrep _ e1
      refine ⟨(c - 1) / N, hri, (c - 1) % N, by rw [cert_pts_size]; exact hsi, ?_, ?_⟩
      · obtain ⟨k1, kc⟩ := conj_dec hK hn (hc _ hsi) cx
        rw [hget _ hsi, hx, k1, eq_dec hK hn kc (hc _ hi)]
        exact e2
      · obtain ⟨k1, kc⟩ := conj_dec hK hn (hc _ hsi) ct
        rw [hget _ hsi, ht, k1, eq_dec hK hn kc (hc _ hj)]
        exact e3
  unfold locCheck
  rw [hbfs]
  have g1 : ((List.range d.gens.size).all fun k => eltValid n d.gens[k]!) = true := by
    rw [List.all_eq_true]
    intro k hk
    rw [hgs] at hk
    have hk' := List.mem_range.1 hk
    rw [(hG' k hk').1]
    exact (valid_dec hK hn (hG' k hk').2).1
  have g2 := arrCertOK_cert Tb hv h0
  rw [hgs] at g1
  have g3 : ((cert m N (fun i => dec n (T i)) E PA LA).pts.size == 2 ^ d.k) = true := by
    rw [cert_pts_size, hk]
    exact beq_self_eq_true _
  have g4 : d.reps.toList.all (repOK n inF) = true := by
    rw [List.all_eq_true]
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    rw [Array.length_toList] at hi
    have := (hrep i (hrs ▸ hi)).1
    rwa [getElem!_pos d.reps i hi, Array.getElem_toList] at *
  rw [hgs]
  simp only [g1, g2, g3, g4, hcov, Bool.and_self]

end CFSG.KS.LocLn

end
