module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Types
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6K

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6FiveK

open CFSG.Permutation.FinPack CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.Setup.X3Aut CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6K

theorem anyK_eq_any (f : ℕ → Bool) (L : List ℕ) : anyK f L = L.any f := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change (f a || anyK f L) = _
    rw [ih, List.any_cons]

theorem exists_of_mem_autK {d : ℕ} (h : d ∈ autK) : ∃ w : AutA6, enc (w : P10) = d := by
  rw [← autK_pin, List.mem_map] at h
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨w, rfl⟩ := exists_of_mem_autL hc
  exact ⟨w, (pk_cd w).symm⟩

theorem cnt_autL_eq (w : AutA6) :
    (Core.autL.filter fun c => Core.cmul (cd w) c == Core.cmul c (cd w)).dedup.length =
      cntL (commLaneK 10 (enc (w : P10))) autK := by
  rw [(autL_nodup.filter _).dedup]
  exact length_filter_autL _ _ fun y => comm_eq w y

theorem cnt_autL_eqP {σ : P10} (hσ : σ ∈ A6Models.autA6) :
    (Core.autL.filter fun c => Core.cmul (code σ) c == Core.cmul c (code σ)).dedup.length =
      cntL (commLaneK 10 (enc σ)) autK :=
  cnt_autL_eq ⟨σ, hσ⟩

theorem beq_natBeq (a b : ℕ) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem ord5_of_mem {a : List ℕ}
    (ha : a ∈ Core.pslLit.filter fun c => Core.cpow c 5 == Core.cid && c != Core.cid) :
    ∃ Y ∈ A6Models.psl29, code Y = a ∧ ord5T (enc Y) = true := by
  rw [List.mem_filter] at ha
  obtain ⟨haP, ha5⟩ := ha
  obtain ⟨Y, hY, rfl⟩ := exists_psl29_of_code haP
  refine ⟨Y, hY, rfl, ?_⟩
  rw [ord5T_eq]
  exact ha5

theorem of_ord5 {f : ℕ → Bool} (h : allK (fun a => !ord5T a || f a) pslK = true) {Y : P10}
    (hY : Y ∈ A6Models.psl29) (h5 : ord5T (enc Y) = true) : f (enc Y) = true := by
  have h1 := allK_iff.1 h _ (enc_mem_pslK hY)
  simp only [h5, Bool.not_true, Bool.false_or] at h1
  exact h1

@[expose] noncomputable def fixes3K (d : ℕ) : Bool :=
  anyK (fun b => commLaneK 10 d b && ord3T b) pslK

theorem fixes3_eq (w : AutA6) : AutA6Types.fixes3 (cd w) = fixes3K (enc (w : P10)) := by
  unfold AutA6Types.fixes3 AutA6Three.ord3P fixes3K
  rw [anyK_eq_any, List.any_filter, ← beq_iff_eq.1 pslK_pin, List.any_map, Bool.eq_iff_iff,
    List.any_eq_true, List.any_eq_true]
  refine exists_congr fun c => and_congr_right fun hc => ?_
  obtain ⟨Z, -, rfl⟩ := exists_psl29_of_code hc
  simp only [Function.comp_apply]
  unfold cd
  rw [pk_code, ord3T_eq, comm_eqP, Bool.and_comm]

@[expose] def y5K : List ℕ :=
  [13222970745, 6026318985, 9485514825, 26442155865, 496375268865, 163347503415, 375886581810,
   154977962355, 483542647080, 504935617590, 307180937985, 227675313735, 169671154020, 151673473350,
   225067962450, 589237153890, 279225918855, 492093597780, 86707303830, 70452061080, 100965500565,
   233412137985, 349009544835, 422131996725, 434219524980, 589485777750, 588729443445, 344194115400,
   289491484965, 370316177700, 296915371875, 588481188135, 78726432915, 430188287745, 418112553090,
   207251543400]

theorem c5psl : allK (fun a => !ord5T a || Nat.beq (cntL (fun d => commLaneK 10 d a) pslK) 5)
    pslK = true := by
  decide +kernel

theorem c5aut : allK (fun a => !ord5T a || Nat.beq (cntL (commLaneK 10 a) autK) 10)
    pslK = true := by
  decide +kernel

theorem inv5A : allK (fun y => memK y y5K || allK (fun a => !commLaneK 10 y a || !ord5T a) pslK)
    invK = true := by
  decide +kernel

theorem mem_y5K {w : AutA6} {Y : P10} (hY : Y ∈ A6Models.psl29) (h5 : ord5T (enc Y) = true)
    (hi : invTK (enc (w : P10)) = true) (hc : commLaneK 10 (enc (w : P10)) (enc Y) = true) :
    memK (enc (w : P10)) y5K = true := by
  have h1 := allK_iff.1 inv5A _ (enc_mem_invK hi)
  cases hm : memK (enc (w : P10)) y5K
  · simp only [hm, Bool.false_or] at h1
    have h2 := allK_iff.1 h1 _ (enc_mem_pslK hY)
    simp only [hc, h5, Bool.not_true, Bool.false_or] at h2
    exact absurd h2 Bool.false_ne_true
  · rfl

theorem c144 : Nat.beq (cntL ord5T pslK) 144 = true := by decide +kernel

theorem inv5B : allK (fun y => Nat.beq (cntL (commLaneK 10 y) autK) 40) y5K = true := by
  decide +kernel

theorem outer5 : allK (fun a => !ord5T a || anyK (fun y => commLaneK 10 y a && invTK y &&
    !memK y pslK && !fixes3K y) y5K) pslK = true := by
  decide +kernel

theorem y5K_sub : allK (fun y => memK y autK) y5K = true := by decide +kernel

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6FiveK
