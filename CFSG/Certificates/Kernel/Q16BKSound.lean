module

public import Certificates.Data.Kernel.Q16BK
public import CFSG.Certificates.Kernel.PGrpMul
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Q16

public section

namespace CFSG.KC.Q16BK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.PGrp
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Monster.B.Co2 (permOfArr eqA_iff rep_idA)
open CFSG.CGT.PushingUpLit.SolKNA.R4 (Q16Pair NoQ16 Q16Pair.map)

variable {n w : ℕ}

@[expose] noncomputable def prodK (n w : ℕ) (L : List ℕ) : ℕ :=
  L.foldr (fun c acc => pcomp n w (mask w) c acc) (pidn n w)

theorem wptK_eq (hsz : szOK n w = true) {x : ℕ} (hx : x < n) :
    ∀ L : List ℕ, wptK w L x = pg w (mask w) (prodK n w L) x
  | [] => (PF.pg_pidn (szOK_facts' hsz).1 (szOK_facts' hsz).2 hx).symm
  | c :: L => by
    have hn : n < 2 ^ 32 := by have := (szOK_facts' hsz).1; omega
    change pg w (mask w) c (wptK w L x) = pg w (mask w) (pcomp n w (mask w) c (prodK n w L)) x
    rw [PF.pg_pcomp hn hx, wptK_eq hsz hx L]

theorem keyWK_eq (hsz : szOK n w = true) (L : List ℕ) :
    ∀ {ps : List ℕ}, (∀ p ∈ ps, p < n) → keyWK n w ps L = BfsPin.keyK n w ps (prodK n w L)
  | [], _ => rfl
  | x :: ps, hps => by
    change Nat.add (wptK w L x) (Nat.mul n (keyWK n w ps L)) =
      Nat.add (pg w (mask w) (prodK n w L) x) (Nat.mul n (BfsPin.keyK n w ps (prodK n w L)))
    rw [wptK_eq hsz (hps x List.mem_cons_self),
      keyWK_eq hsz L fun y hy => hps y (List.mem_cons_of_mem x hy)]

theorem prodK_facts (hsz : szOK n w = true) {gs : Array (Array ℕ)} :
    ∀ L : List ℕ, (∀ c ∈ L, permB n w c = true ∧
        permOfArr n (unpack n w c) ∈ Subgroup.closure (permsA n gs)) →
      permB n w (prodK n w L) = true ∧
        permOfArr n (unpack n w (prodK n w L)) ∈ Subgroup.closure (permsA n gs) ∧
        permOfArr n (unpack n w (prodK n w L)) = (L.map fun c => permOfArr n (unpack n w c)).prod
  | [], _ => ⟨permB_of_pp (PP.id hsz), mem_id hsz, by
      rw [List.map_nil, List.prod_nil]
      change permOfArr n (unpack n w (pidn n w)) = 1
      rw [← idA_eq hsz, permOfArr_eq_of_rep rep_idA]⟩
  | c :: L, hL => by
    obtain ⟨h1, h2, h3⟩ := prodK_facts hsz L fun d hd => hL d (List.mem_cons_of_mem c hd)
    obtain ⟨hc1, hc2⟩ := hL c List.mem_cons_self
    refine ⟨permB_pcomp hsz hc1 h1, mem_mul hsz hc1 h1 hc2 h2, ?_⟩
    change permOfArr n (unpack n w (pcomp n w (mask w) c (prodK n w L))) = _
    rw [permOfArr_pcomp hsz hc1 h1, h3, List.map_cons, List.prod_cons]

theorem prod_eq_iff_keyWK (hsz : szOK n w = true) {gs : Array (Array ℕ)} {ps : List ℕ}
    {c : ArrCert} (hps : ∀ p ∈ ps, p < n) (h : enumOK n gs ps c = true) {L₁ L₂ : List ℕ}
    (h₁ : ∀ c ∈ L₁, permB n w c = true ∧
      permOfArr n (unpack n w c) ∈ Subgroup.closure (permsA n gs))
    (h₂ : ∀ c ∈ L₂, permB n w c = true ∧
      permOfArr n (unpack n w c) ∈ Subgroup.closure (permsA n gs)) :
    (L₁.map fun c => permOfArr n (unpack n w c)).prod =
        (L₂.map fun c => permOfArr n (unpack n w c)).prod ↔
      keyWK n w ps L₁ = keyWK n w ps L₂ := by
  obtain ⟨a₁, b₁, e₁⟩ := prodK_facts hsz L₁ h₁
  obtain ⟨a₂, b₂, e₂⟩ := prodK_facts hsz L₂ h₂
  rw [← e₁, ← e₂, keyWK_eq hsz L₁ hps, keyWK_eq hsz L₂ hps,
    ← eqA_iff (rep_of_validA (BfsPin.validA_unpack a₁)) (rep_of_validA (BfsPin.validA_unpack a₂)),
    eqA_unpack' hsz a₁ a₂, beq_iff_keyK hsz hps h a₁ a₂ b₁ b₂, Nat.beq_eq]

theorem q16BK_sound {ng N nR : ℕ} {G T E S RI C W : ℕ → ℕ} {SK ps : List ℕ}
    {gs : Array (Array ℕ)} (hs : gs.size = ng) (hg : ∀ k < ng, gs[k]! = unpack n w (G k))
    (hp : ∀ k < ng, permB n w (G k) = true) (hk : bfsK n w ng G N T E S = true)
    (hps : ∀ p ∈ ps, p < n) (hK : keysSK n w ps N T SK = true)
    (hq : q16BK n w ps N T nR RI C W = true) :
    Nat.card (Subgroup.closure (permsA n gs)) = N ∧
      NoQ16 ↥(Subgroup.closure (permsA n gs)) := by
  have hsz : szOK n w = true := by
    have hk' := hk
    unfold bfsK at hk'
    simp only [bAnd_iff] at hk'
    exact hk'.1
  have hok : enumOK n gs ps (enumBfs n gs ps N) = true :=
    enumOK_of_bfsK_base hs hg hp hk hps hK le_rfl
  have hpts := enumBfs_pts_base hs hg hk hps hK (le_refl N)
  have hsize : (enumBfs n gs ps N).pts.size = N := by rw [hpts, Array.size_ofFn]
  have hget : ∀ i < N, (enumBfs n gs ps N).pts[i]! = unpack n w (T i) := fun i hi => by
    rw [hpts, getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]
  obtain ⟨hmem, hcard, -⟩ := enumOK_spec hps hok
  refine ⟨hcard.trans hsize, ?_⟩
  have gd : ∀ i < N, permB n w (T i) = true ∧
      permOfArr n (unpack n w (T i)) ∈ Subgroup.closure (permsA n gs) := fun i hi =>
    ⟨permB_of_pp (PP_pts hk hp i hi), mem_of_pt hsz hps hok hsize hget hi⟩
  have ex : ∀ z ∈ Subgroup.closure (permsA n gs), ∃ i < N, permOfArr n (unpack n w (T i)) = z :=
      fun z hz => by
    obtain ⟨i, hi, e⟩ := (hmem z).1 hz
    rw [hsize] at hi
    exact ⟨i, hi, by rw [← hget i hi, e]⟩
  have kE := fun {L₁ L₂ : List ℕ} => prod_eq_iff_keyWK (L₁ := L₁) (L₂ := L₂) hsz hps hok
  clear hmem hcard hpts
  rw [q16BK, PF.strictB_eqP, bAnd_iff] at hq
  obtain ⟨hpt, hrep⟩ := hq
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hpair
  have hxy : Q16Pair x y :=
    Q16Pair.map (Subgroup.closure (permsA n gs)).subtype Subtype.val_injective hpair
  obtain ⟨i, hi, rfl⟩ := ex x hx
  obtain ⟨g1, g2⟩ := gd i hi
  have hpi := allN_spec hpt i hi
  unfold ptQ at hpi
  rw [PF.strictB_eqP] at hpi
  obtain ⟨u, hu⟩ : ∃ u, permOfArr n (unpack n w (T i)) = u := ⟨_, rfl⟩
  rw [hu] at hxy
  have h1 := hxy.1
  have h2 := hxy.2.1
  cases hb4 : Nat.beq (keyWK n w ps [T i, T i, T i, T i]) (keyWK n w ps [])
  · rw [hb4] at hpi
    dsimp only at hpi
    cases hb8 : Nat.beq (keyWK n w ps [T i, T i, T i, T i, T i, T i, T i, T i]) (keyWK n w ps [])
    · have k8 := (kE (L₁ := [T i, T i, T i, T i, T i, T i, T i, T i]) (L₂ := [])
        (by simp [g1, g2]) (by simp)).1 (by
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hu]
          rw [← h2]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc])
      rw [k8, Nat.beq_refl] at hb8
      exact Bool.noConfusion hb8
    rw [hb8] at hpi
    dsimp only at hpi
    rw [PF.strictB_eqP, PF.strictB_eqP, bAnd_iff, bAnd_iff, PF.strictB_eqP] at hpi
    obtain ⟨hc, hj, hkey⟩ := hpi
    have hc' := Nat.blt_eq.mp hc
    have hj' := Nat.blt_eq.mp hj
    have hr := allN_spec hrep (C i) hc'
    rw [bAnd_iff] at hr
    obtain ⟨hRI, hR⟩ := hr
    have hRI' := Nat.blt_eq.mp hRI
    obtain ⟨gW1, gW2⟩ := gd (W i) hj'
    obtain ⟨gR1, gR2⟩ := gd (RI (C i)) hRI'
    have hgu0 := (kE (L₁ := [T (W i), T i]) (L₂ := [T (RI (C i)), T (W i)])
        (by simp [g1, g2, gW1, gW2]) (by simp [gR1, gR2, gW1, gW2])).2
        (Nat.eq_of_beq_eq_true hkey)
    obtain ⟨g, hg⟩ : ∃ g, permOfArr n (unpack n w (T (W i))) = g := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, permOfArr n (unpack n w (T (RI (C i)))) = r := ⟨_, rfl⟩
    have hgu : g * u = r * g := by
      simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hu, hg,
        hr] using hgu0
    have hy' : g * y * g⁻¹ ∈ Subgroup.closure (permsA n gs) := by
      rw [← hg]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ gW2 hy) (Subgroup.inv_mem _ gW2)
    obtain ⟨j, hjN, hyj⟩ := ex _ hy'
    obtain ⟨gj1, gj2⟩ := gd j hjN
    obtain ⟨v, hv⟩ : ∃ v, permOfArr n (unpack n w (T j)) = v := ⟨_, rfl⟩
    rw [hv] at hyj
    have hq' := Q16Pair.map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective hxy
    have hcu : (MulAut.conj g).toMonoidHom u = r := by
      change g * u * g⁻¹ = r
      rw [hgu]
      group
    have hcy : (MulAut.conj g).toMonoidHom y = v := by
      change g * y * g⁻¹ = v
      rw [hyj]
    rw [hcu, hcy] at hq'
    obtain ⟨-, -, e3, e4⟩ := hq'
    unfold repQ at hR
    rw [PF.strictB_eqP] at hR
    have hRj := allN_spec hR j hjN
    rw [PF.strictB_eqP] at hRj
    have kb2 : Nat.beq (keyWK n w ps [T j, T j])
        (keyWK n w ps [T (RI (C i)), T (RI (C i)), T (RI (C i)), T (RI (C i))]) = true := by
      rw [Nat.beq_eq]
      refine (kE (by simp [gj1, gj2]) (by simp [gR1, gR2])).1 ?_
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hv, hr]
      rw [← sq, e3]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    have kb3 : Nat.beq (keyWK n w ps [T (RI (C i)), T j, T (RI (C i))]) (keyWK n w ps [T j]) =
        true := by
      rw [Nat.beq_eq]
      refine (kE (by simp [gj1, gj2, gR1, gR2]) (by simp [gj1, gj2])).1 ?_
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hv, hr]
      have e4' : v * r = r⁻¹ * v := by
        calc v * r = v * r * v⁻¹ * v := by group
          _ = r⁻¹ * v := by rw [e4]
      rw [e4']
      group
    rw [kb2, kb3] at hRj
    exact Bool.noConfusion hRj
  · have k4 := (kE (L₁ := [T i, T i, T i, T i]) (L₂ := []) (by simp [g1, g2]) (by simp)).2
      (Nat.eq_of_beq_eq_true hb4)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hu] at k4
    exact h1 (by rw [← k4]; simp only [pow_succ, pow_zero, one_mul, mul_assoc])

end CFSG.KC.Q16BK

end
