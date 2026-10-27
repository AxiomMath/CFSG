module

public import Certificates.Data.Kernel.LocalQT.Lat7
public import CFSG.Certificates.Kernel.LocalQTBfsKSound
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Comp
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Make

public section

namespace CFSG.KC.LQT.L

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.KS.PK

variable {n : ℕ}

def rnc7 (r : RN n) : ℕ := enc 7 (rdig r) n

def code7 (σ : Perm (Fin n)) : ℕ := enc 7 (P.vals σ) n

theorem rnc7_eq_enc (r : RN n) : rnc7 r = enc 7 (rdig r) n := by rw [rnc7]

theorem mul7_eq (hn : n ≤ 128) (s t : ℕ) : mul7 n s t = enc 7 (fun i => fd 7 s (fd 7 t i)) n :=
  pcomp_eq (by omega) 7 s t

theorem one7_eq (hn : n ≤ 128) : one7 n = enc 7 (fun i => i) n :=
  pidn_eq (le_trans hn (by norm_num)) (le_trans hn (by norm_num))

theorem rdig_lt7 (hn : n ≤ 128) (r : RN n) : ∀ i < n, rdig r i < 2 ^ 7 := fun i hi => by
  rw [rdig_of_lt r hi]
  have := (r.val[(⟨i, hi⟩ : Fin n)]).isLt
  have h7 : (2 : ℕ) ^ 7 = 128 := by norm_num
  rw [h7]
  omega

theorem fd_rnc7 (hn : n ≤ 128) (r : RN n) (i : Fin n) : fd 7 (rnc7 r) i = (r.val[i] : ℕ) := by
  rw [rnc7, fd_enc (rdig_lt7 hn r) i.isLt, rdig_of_lt r i.isLt]

theorem rnc7_enc (σ : Perm (Fin n)) : rnc7 (RN.enc σ) = code7 σ := by
  rw [rnc7, code7]
  refine enc_congr fun i hi => ?_
  rw [rdig_of_lt _ hi, RN.enc_get]
  exact (P.vals_fin σ ⟨i, hi⟩).symm

theorem code7_of_getD (σ : Perm (Fin n)) {l : List ℕ} (h : ∀ i : Fin n, (σ i : ℕ) = l.getD i 0) :
    code7 σ = enc 7 (fun i => l.getD i 0) n := by
  rw [code7]
  refine enc_congr fun i hi => ?_
  rw [← h ⟨i, hi⟩]
  exact P.vals_fin σ ⟨i, hi⟩

theorem rnc7_mul (hn : n ≤ 128) (x y : RN n) : rnc7 (x * y) = mul7 n (rnc7 x) (rnc7 y) := by
  rw [mul7_eq hn, rnc7]
  refine enc_congr fun i hi => ?_
  rw [rdig_of_lt _ hi, RN.mul_get, fd_rnc7 hn y ⟨i, hi⟩, fd_rnc7 hn x]

theorem rnc7_one (hn : n ≤ 128) : rnc7 (1 : RN n) = one7 n := by
  rw [one7_eq hn, rnc7]
  refine enc_congr fun i hi => ?_
  rw [rdig_of_lt _ hi, RN.one_get]

theorem rnc7_inj (hn : n ≤ 128) : Function.Injective (rnc7 : RN n → ℕ) := by
  intro x y h
  refine RN.ext fun i => Fin.ext ?_
  have := fd_rnc7 hn x i
  rw [h, fd_rnc7 hn y i] at this
  exact this.symm

theorem beq_rnc7 (hn : n ≤ 128) (x y : RN n) : (x == y) = Nat.beq (rnc7 x) (rnc7 y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, P.beq_iff, (rnc7_inj hn).eq_iff]

theorem map_rnc7_enc (L : List (Perm (Fin n))) : (L.map RN.enc).map rnc7 = L.map code7 := by
  rw [List.map_map]
  exact List.map_congr_left fun σ _ => rnc7_enc σ

theorem rep_bfsK7 (hn : n ≤ 128) (L : List (Perm (Fin n))) (d : ℕ) :
    Rep rnc7 (bfsK7 n (L.map code7) d) (bfsSet (L.map RN.enc) d) := by
  have := rep_bfs (rnc7_inj hn) (mul7 n) (rnc7_mul hn) (L.map RN.enc) d
  rwa [map_rnc7_enc, rnc7_one hn] at this

theorem closedK7_eq (hn : n ≤ 128) (L : List (Perm (Fin n))) (d : ℕ) :
    closedK7 n (L.map code7) (bfsK7 n (L.map code7) d) =
      closedH (L.map RN.enc) (bfsSet (L.map RN.enc) d) := by
  have := closedG_eq (rnc7_inj hn) (mul7 n) (rnc7_mul hn) (L.map RN.enc) (rep_bfsK7 hn L d)
  rwa [map_rnc7_enc, rnc7_one hn] at this

theorem size_bfsK7 (hn : n ≤ 128) (L : List (Perm (Fin n))) (d : ℕ) :
    (bfsK7 n (L.map code7) d).size = (bfsSet (L.map RN.enc) d).size :=
  rep_size (rep_bfsK7 hn L d)

theorem contains_bfsK7 (hn : n ≤ 128) (L : List (Perm (Fin n))) (d : ℕ) (r : RN n) :
    (bfsSet (L.map RN.enc) d).contains r = memT (bfsK7 n (L.map code7) d).t (rnc7 r) := by
  rw [Bool.eq_iff_iff, Std.HashSet.contains_iff_mem, rep_mem_iff (rnc7_inj hn) (rep_bfsK7 hn L d)]

end CFSG.KC.LQT.L

end
