module

public import Certificates.Data.Kernel.PermCent.Sz8DC
public import CFSG.Certificates.Kernel.PermCent.KGrpCSound
public import CFSG.GH74.KGroups.Checks

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5129

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.Sz8
  CFSG.GH74.KGroups.Sz8D CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.PkCV

section Generic

variable {Gp : Type*} [Group Gp]

theorem comm_central (L : Set Gp)
    (h : ∀ a ∈ L, ∀ b ∈ L,
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Subgroup.closure L : Set Gp)) :
    ∀ a ∈ Subgroup.closure L, ∀ b ∈ Subgroup.closure L,
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Subgroup.closure L : Set Gp) := by
  have hcomm : ∀ z ∈ Subgroup.centralizer (Subgroup.closure L : Set Gp),
      ∀ c ∈ Subgroup.closure L, c * z * c⁻¹ = z := by
    intro z hz c hc
    rw [Subgroup.mem_centralizer_iff.1 hz c hc, mul_inv_cancel_right]
  have hA : ∀ a ∈ L, ∀ b ∈ Subgroup.closure L,
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Subgroup.closure L : Set Gp) := by
    intro a ha b hb
    induction hb using Subgroup.closure_induction with
    | mem x hx => exact h a ha x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
      have e : a * (x * y) * a⁻¹ * (x * y)⁻¹ =
          (a * x * a⁻¹ * x⁻¹) * (x * (a * y * a⁻¹ * y⁻¹) * x⁻¹) := by group
      rw [e, hcomm _ ihy x hx]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx =>
      have e : a * x⁻¹ * a⁻¹ * x⁻¹⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
      rw [e, hcomm _ (Subgroup.inv_mem _ ihx) _ (Subgroup.inv_mem _ hx)]
      exact Subgroup.inv_mem _ ihx
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hA x hx
  | one => intro b _; simp
  | mul x y hx hy ihx ihy =>
    intro b hb
    have e : x * y * b * (x * y)⁻¹ * b⁻¹ =
        x * (y * b * y⁻¹ * b⁻¹) * x⁻¹ * (x * b * x⁻¹ * b⁻¹) := by group
    rw [e, hcomm _ (ihy b hb) x hx]
    exact Subgroup.mul_mem _ (ihy b hb) (ihx b hb)
  | inv x hx ihx =>
    intro b hb
    have e : x⁻¹ * b * x⁻¹⁻¹ * b⁻¹ = x⁻¹ * (x * b * x⁻¹ * b⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e, hcomm _ (Subgroup.inv_mem _ (ihx b hb)) _ (Subgroup.inv_mem _ hx)]
    exact Subgroup.inv_mem _ (ihx b hb)

theorem mem_centralizer_closure (L : Set Gp) (z : Gp) (h : ∀ c ∈ L, c * z = z * c) :
    z ∈ Subgroup.centralizer (Subgroup.closure L : Set Gp) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hle : Subgroup.closure L ≤ Subgroup.centralizer ({z} : Set Gp) :=
    (Subgroup.closure_le _).2 fun c hc => Subgroup.mem_centralizer_singleton_iff.2 (h c hc)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

theorem mem_of_nodup_card (K : Subgroup Gp) [Finite K] (L : List Gp) (hL : L.Nodup)
    (hsub : ∀ x ∈ L, x ∈ K) (hcard : Nat.card K ≤ L.length) : ∀ x ∈ K, x ∈ L := by
  classical
  intro x hx
  by_contra hxL
  have hnd : (x :: L).Nodup := List.nodup_cons.2 ⟨hxL, hL⟩
  have hsub' : ((x :: L).toFinset : Set Gp) ⊆ (K : Set Gp) := by
    intro y hy
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact hsub y hy
  have h1 := Set.ncard_le_ncard hsub' (Set.toFinite _)
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, ← Nat.card_coe_set_eq] at h1
  simp only [List.length_cons] at h1
  have : Nat.card (K : Set Gp) = Nat.card K := rfl
  omega

variable [Finite Gp]

theorem le_of_card448 {B N : Subgroup Gp} (hNB : N ≤ B) (hB : Nat.card B = 448)
    (h64 : 64 ∣ Nat.card N) {t : Gp} (ht : t ∈ N) (ht7 : orderOf t = 7) : B ≤ N := by
  have h7 : 7 ∣ Nat.card N := ht7 ▸ Subgroup.orderOf_dvd_natCard N ht
  have h448 : 448 ∣ Nat.card N :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h64 h7
  have hle : Nat.card N ≤ 448 := hB ▸ Subgroup.card_le_of_le hNB
  have hpos : 0 < Nat.card N := Nat.card_pos
  have := Nat.le_of_dvd hpos h448
  exact (Subgroup.eq_of_le_of_card_ge hNB (by omega)).ge

theorem conj_mem_of_normal {S B : Subgroup Gp} (hSB : S ≤ B)
    (hBN : B ≤ Subgroup.normalizer (S : Set Gp)) (hS : Nat.card S = 64) (hB : Nat.card B = 448)
    (g : Gp) (hg : ∀ b ∈ B, g * b * g⁻¹ ∈ B) : ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' := S.map (MulAut.conj g).toMonoidHom with hS'
  have hS'B : S' ≤ B := by
    rintro _ ⟨s, hs, rfl⟩
    exact hg s (hSB hs)
  have hp : IsPGroup 2 S := IsPGroup.of_card (n := 6) (by rw [hS]; norm_num)
  have hp' : IsPGroup 2 S' := hp.map _
  have hsup := hp.to_sup_of_normal_left' hp' (hS'B.trans hBN)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hsup
  have hdvd : 2 ^ k ∣ 448 := hk ▸ hB ▸ Subgroup.card_dvd_of_le (sup_le hSB hS'B)
  have hk6 : k ≤ 6 := by
    by_contra hk7
    have : 2 ^ 7 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := Nat.dvd_trans this hdvd
    norm_num at this
  have hle : Nat.card ↥(S ⊔ S') ≤ Nat.card S := by
    rw [hk, hS]
    calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hk6
      _ = 64 := by norm_num
  have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : S ≤ S ⊔ S') hle
  intro s hs
  have : g * s * g⁻¹ ∈ S' := ⟨s, hs, rfl⟩
  rw [heq]
  exact Subgroup.mem_sup_right this

theorem conj_mem_center {S : Subgroup Gp} (g : Gp) (h1 : ∀ s ∈ S, g * s * g⁻¹ ∈ S)
    (h2 : ∀ s ∈ S, g⁻¹ * s * g⁻¹⁻¹ ∈ S) :
    ∀ t ∈ S ⊓ Subgroup.centralizer (S : Set Gp),
      g * t * g⁻¹ ∈ S ⊓ Subgroup.centralizer (S : Set Gp) := by
  intro t ht
  obtain ⟨htS, htC⟩ := Subgroup.mem_inf.1 ht
  refine Subgroup.mem_inf.2 ⟨h1 t htS, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
  obtain ⟨s', hs', rfl⟩ : ∃ s' ∈ S, s = g * s' * g⁻¹ :=
    ⟨g⁻¹ * s * g⁻¹⁻¹, h2 s hs, by group⟩
  have hc : s' * t = t * s' := Subgroup.mem_centralizer_iff.1 htC s' hs'
  calc g * s' * g⁻¹ * (g * t * g⁻¹) = g * (s' * t) * g⁻¹ := by group
    _ = g * (t * s') * g⁻¹ := by rw [hc]
    _ = g * t * g⁻¹ * (g * s' * g⁻¹) := by group

theorem inv_all {S E B A₀ : Subgroup Gp} (κ : Gp → Gp → ZMod 2) (hSB : S ≤ B) (hBA : B ≤ A₀)
    (hS : Nat.card S = 64) (hB : Nat.card B = 448) (hA : Nat.card A₀ = 1344)
    (hN : ∀ g ∈ A₀, ∀ s ∈ S, g * s * g⁻¹ ∈ S) (hNE : ∀ g ∈ A₀, ∀ t ∈ E, g * t * g⁻¹ ∈ E)
    (hinvS : ∀ g ∈ S, ∀ s ∈ S, ∀ t ∈ E, κ (g * s * g⁻¹) (g * t * g⁻¹) = κ s t)
    {tt σ : Gp} (htB : tt ∈ B) (ht7 : orderOf tt = 7)
    (hinvt : ∀ s ∈ S, ∀ t ∈ E, κ (tt * s * tt⁻¹) (tt * t * tt⁻¹) = κ s t)
    (hσA : σ ∈ A₀) (hσB : σ ∉ B)
    (hinvσ : ∀ s ∈ S, ∀ t ∈ E, κ (σ * s * σ⁻¹) (σ * t * σ⁻¹) = κ s t) :
    ∀ g ∈ A₀, ∀ s ∈ S, ∀ t ∈ E, κ (g * s * g⁻¹) (g * t * g⁻¹) = κ s t := by
  let H : Subgroup Gp :=
    { carrier := {g | g ∈ A₀ ∧ ∀ s ∈ S, ∀ t ∈ E, κ (g * s * g⁻¹) (g * t * g⁻¹) = κ s t}
      mul_mem' := by
        rintro g h ⟨hg, hgi⟩ ⟨hh, hhi⟩
        refine ⟨Subgroup.mul_mem _ hg hh, fun s hs t ht => ?_⟩
        have e1 : g * h * s * (g * h)⁻¹ = g * (h * s * h⁻¹) * g⁻¹ := by group
        have e2 : g * h * t * (g * h)⁻¹ = g * (h * t * h⁻¹) * g⁻¹ := by group
        rw [e1, e2, hgi _ (hN h hh s hs) _ (hNE h hh t ht), hhi s hs t ht]
      one_mem' := ⟨Subgroup.one_mem _, fun s _ t _ => by simp⟩
      inv_mem' := by
        rintro g ⟨hg, hgi⟩
        refine ⟨Subgroup.inv_mem _ hg, fun s hs t ht => ?_⟩
        have := hgi _ (hN _ (Subgroup.inv_mem _ hg) s hs) _ (hNE _ (Subgroup.inv_mem _ hg) t ht)
        have e1 : g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ = s := by group
        have e2 : g * (g⁻¹ * t * g⁻¹⁻¹) * g⁻¹ = t := by group
        rw [e1, e2] at this
        exact this.symm }
  have hHA : H ≤ A₀ := fun g hg => hg.1
  have hSH : S ≤ H := fun g hg => ⟨hBA (hSB hg), hinvS g hg⟩
  have hBH : B ≤ H := by
    have h64 : 64 ∣ Nat.card ↥(H ⊓ B) :=
      hS ▸ Subgroup.card_dvd_of_le (le_inf hSH hSB)
    exact (le_of_card448 inf_le_right hB h64 (Subgroup.mem_inf.2 ⟨⟨hBA htB, hinvt⟩, htB⟩)
      ht7).trans inf_le_left
  have hσH : σ ∈ H := ⟨hσA, hinvσ⟩
  have h1 : 448 ∣ Nat.card H := hB ▸ Subgroup.card_dvd_of_le hBH
  have h2 : Nat.card H ∣ 1344 := hA ▸ Subgroup.card_dvd_of_le hHA
  have h3 : Nat.card H ≠ 448 := by
    intro h
    exact hσB ((Subgroup.eq_of_le_of_card_ge hBH (by omega)).ge hσH)
  have hpos : 0 < Nat.card H := Nat.card_pos
  have h4 : Nat.card H = 1344 := by
    have hle := Nat.le_of_dvd (by norm_num) h2
    obtain ⟨k, hk⟩ := h1
    obtain ⟨m, hm⟩ := h2
    rw [hk] at hm h3 hpos hle ⊢
    have hk3 : k ≤ 3 := by omega
    interval_cases k <;> omega
  have hHA' := Subgroup.eq_of_le_of_card_ge hHA (by omega)
  intro g hg
  exact (hHA'.ge hg).2

end Generic

theorem card_stab_mul {α : Type*} [Fintype α] [DecidableEq α] (K : Subgroup (Equiv.Perm α))
    (c : α) (htr : ∀ i, ∃ g ∈ K, g c = i) :
    Nat.card ↥(K ⊓ MulAction.stabilizer (Equiv.Perm α) c) * Fintype.card α = Nat.card K := by
  have horb : MulAction.orbit K c = Set.univ := by
    ext i
    simp only [Set.mem_univ, iff_true]
    obtain ⟨g, hg, rfl⟩ := htr i
    exact ⟨⟨g, hg⟩, rfl⟩
  have e : MulAction.stabilizer K c ≃ ↥(K ⊓ MulAction.stabilizer (Equiv.Perm α) c) :=
    { toFun := fun g => ⟨g.1.1, Subgroup.mem_inf.2 ⟨g.1.2, g.2⟩⟩
      invFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩, (Subgroup.mem_inf.1 g.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e, ← Subgroup.card_mul_index (MulAction.stabilizer K c),
    MulAction.index_stabilizer, horb, Set.ncard_univ, Nat.card_eq_fintype_card (α := α)]

local notation "Pm" => Equiv.Perm (Fin 65)

local notation "Lsy" => [sy0, sy1, sy2, sy3, sy4, sy5]

theorem allVec3_mem (v : Fin 3 → ZMod 2) : v ∈ allVec3 := by
  revert v
  decide +kernel

theorem allU_mem (u : Fin 3 → Fin 3 → ZMod 2) : u ∈ allU := by
  have h : u = ![u 0, u 1, u 2] := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  simp only [allU, List.mem_flatMap, List.mem_map]
  exact ⟨u 0, allVec3_mem _, u 1, allVec3_mem _, u 2, allVec3_mem _, rfl⟩

theorem ev_xsC (i : Fin 3) : ev (xsC i) = xs i := by
  fin_cases i <;> simp [xsC, xs, ev_cOf, tab_eq]

theorem ev_ysC (j : Fin 3) : ev (ysC j) = ys j := by
  fin_cases j <;> simp [ysC, ys, ev_cOf, tab_eq]

theorem ev_pr3 (c : Fin 3 → CV 65) (a : Fin 3 → ZMod 2) :
    ev (pr3 c a) = pr3 (fun i => ev (c i)) a := by
  simp only [pr3, ev_mul, ← ev_pow']

theorem pr3_xs (a : Fin 3 → ZMod 2) : pr3 xs a = ev (pr3 xsC a) := by
  rw [ev_pr3]
  congr 1
  funext i
  exact (ev_xsC i).symm

theorem pr3_ys (b : Fin 3 → ZMod 2) : pr3 ys b = ev (pr3 ysC b) := by
  rw [ev_pr3]
  congr 1
  funext i
  exact (ev_ysC i).symm

theorem of_eq22C {a b c d : CV 65} (h : eq22C a b c d = true) : ev a * ev b = ev c * ev d := by
  rw [eq22C_eq] at h
  rw [ev_mul', ev_mul', of_decide_eq_true h]

theorem mem_of_siftC {Q : RawSchreierDatum 65} (hQ : ValidSchreier Q) {c : CV 65}
    (h : siftC Q c 0 = true) : ev c ∈ Q.originalSubgroup :=
  (mem_iff_sift Q hQ _).2 (by rw [sift_ev]; exact h)

theorem QS_valid_of (h : schP QS = true) : ValidSchreier QS := by
  have h' := h
  unfold QS at h' ⊢
  exact check_certificate_of _ _ _ _ _ h'

theorem card_S_of (hQS : ValidSchreier QS) (h : orderV QS = 64) :
    Nat.card QS.originalSubgroup = 64 := by
  rw [card_group QS hQS, orderCertificate_eq_orderV, h]

theorem S_closure : QS.originalSubgroup = Subgroup.closure {g | g ∈ Lsy} := by
  rw [QS, certificate_originalSubgroup]

theorem A_closure : QA.originalSubgroup = Subgroup.closure {g | g ∈ [pa, pb, sg0]} := by
  rw [QA, certificate_originalSubgroup]

theorem P_le_A : QP.originalSubgroup ≤ QA.originalSubgroup := by
  rw [QP_closure, A_closure, Subgroup.closure_le]
  intro g hg
  apply Subgroup.subset_closure
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl <;> simp

theorem mem_syC {a : Pm} (ha : a ∈ Lsy) : cOf a ∈ syC := List.mem_map_of_mem ha

theorem S_le_P (hP : ValidSchreier QP) (h : syC.all (fun c => siftC QP c 0) = true) :
    QS.originalSubgroup ≤ QP.originalSubgroup := by
  rw [S_closure, Subgroup.closure_le]
  intro a ha
  have := mem_of_siftC hP (List.all_eq_true.1 h _ (mem_syC ha))
  rwa [ev_cOf] at this

theorem mem_S_iff (hQS : ValidSchreier QS) (s : Pm) :
    s ∈ QS.originalSubgroup ↔ ∃ c ∈ elemsC QS, ev c = s := by
  rw [← mem_elemsT QS hQS, elemsT_eq_elemsC, List.mem_map]

theorem S_fix_of (hQS : ValidSchreier QS) (h : orbOK 37 40 = true) :
    ∀ s ∈ QS.originalSubgroup, s cpt = cpt := by
  intro s hs
  obtain ⟨c, hc, rfl⟩ := (mem_S_iff hQS s).1 hs
  have h1 := List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).1 c hc
  apply Fin.ext
  rw [ev_apply]
  exact beq_iff_eq.1 h1

theorem S_orbit_of (hQS : ValidSchreier QS) (h : orbOK 37 40 = true) :
    ∀ i : Fin 65, i ≠ cpt → ∃ s ∈ QS.originalSubgroup, s 40 = i := by
  intro i hi
  have h1 := List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).2 i.val (List.mem_range.2 i.2)
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact absurd (Fin.ext (beq_iff_eq.1 h1)) hi
  · obtain ⟨c, hc, h2⟩ := List.any_eq_true.1 h1
    refine ⟨ev c, (mem_S_iff hQS _).2 ⟨c, hc, rfl⟩, Fin.ext ?_⟩
    rw [ev_apply]
    exact beq_iff_eq.1 h2

theorem fix_unique_of (hQS : ValidSchreier QS) (h : orbOK 37 40 = true) :
    ∀ i : Fin 65, (∀ s ∈ QS.originalSubgroup, s i = i) → i = cpt := by
  intro i hi
  by_contra hne
  obtain ⟨s, hs, hsi⟩ := S_orbit_of hQS h i hne
  have h40 : i = 40 := by
    have h0 := hi s⁻¹ (Subgroup.inv_mem _ hs)
    have h1 : s⁻¹ (s 40) = 40 := by simp
    rw [hsi, h0] at h1
    exact h1
  obtain ⟨s', hs', hs'i⟩ := S_orbit_of hQS h 41 (by decide)
  have := hi s' hs'
  rw [h40, hs'i] at this
  exact absurd this (by decide)

theorem ys_S (hQS : ValidSchreier QS) (h : (List.finRange 3).all (fun j => siftC QS (ysC j) 0) = true) :
    ∀ j, ys j ∈ QS.originalSubgroup := by
  intro j
  rw [← ev_ysC]
  exact mem_of_siftC hQS (List.all_eq_true.1 h j (List.mem_finRange j))

theorem xs_S (hQS : ValidSchreier QS) (h : (List.finRange 3).all (fun i => siftC QS (xsC i) 0) = true) :
    ∀ i, xs i ∈ QS.originalSubgroup := by
  intro i
  rw [← ev_xsC]
  exact mem_of_siftC hQS (List.all_eq_true.1 h i (List.mem_finRange i))

theorem ys_mem_of (hQS : ValidSchreier QS)
    (h : (List.finRange 3).all (fun j => siftC QS (ysC j) 0) = true) (hc : ysCentOK = true) :
    ∀ j, ys j ∈ QS.originalSubgroup ⊓
      Subgroup.centralizer (QS.originalSubgroup : Set Pm) := by
  intro j
  refine Subgroup.mem_inf.2 ⟨ys_S hQS h j, ?_⟩
  rw [S_closure]
  apply mem_centralizer_closure
  intro a ha
  have h1 := of_eq22C (List.all_eq_true.1 (List.all_eq_true.1 hc j (List.mem_finRange j)) _
    (mem_syC ha))
  rw [ev_ysC, ev_cOf] at h1
  exact h1.symm

theorem ys0_ne_of (h : ysC 0 ≠ 1) : ys 0 ≠ 1 := by
  rw [← ev_ysC, ← ev_one]
  exact fun h' => h (ev_injective h')

theorem comm_S (hc : commOK = true) :
    ∀ a ∈ QS.originalSubgroup, ∀ b ∈ QS.originalSubgroup,
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (QS.originalSubgroup : Set Pm) := by
  rw [S_closure]
  apply comm_central
  intro a ha b hb
  apply mem_centralizer_closure
  intro c hc'
  have h1 := of_eq22C (List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 hc _
    (mem_syC ha)) _ (mem_syC hb)) _ (mem_syC hc'))
  simp only [ev_mul, ev_inv, ev_cOf] at h1
  exact h1.symm

theorem dec_of (hQS : ValidSchreier QS) (hS : Nat.card QS.originalSubgroup = 64)
    (hx : ∀ i, xs i ∈ QS.originalSubgroup) (hy : ∀ j, ys j ∈ QS.originalSubgroup)
    (hdec : decOK = true) :
    ∀ s ∈ QS.originalSubgroup, ∃ a b : Fin 3 → ZMod 2, s = pr3 xs a * pr3 ys b := by
  have hnd : (allVec3.flatMap fun a => allVec3.map fun b => pr3 xs a * pr3 ys b).Nodup := by
    unfold decOK at hdec
    have h0 := of_decide_eq_true hdec
    have e1 : (allVec3.flatMap fun a => allVec3.map fun b => (pr3 xsC a * pr3 ysC b).1) =
        (allVec3.flatMap fun a => allVec3.map fun b => pr3 xsC a * pr3 ysC b).map
          Subtype.val := by
      rw [List.map_flatMap]
      simp only [List.map_map]
      rfl
    have e2 : (allVec3.flatMap fun a => allVec3.map fun b => pr3 xs a * pr3 ys b) =
        (allVec3.flatMap fun a => allVec3.map fun b => pr3 xsC a * pr3 ysC b).map ev := by
      rw [List.map_flatMap]
      simp only [List.map_map, Function.comp_def, ev_mul, ← pr3_xs, ← pr3_ys]
    rw [e1] at h0
    rw [e2]
    exact (List.Nodup.of_map _ h0).map ev_injective
  have hall := mem_of_nodup_card QS.originalSubgroup _ hnd (by
    intro x hx'
    obtain ⟨a, -, hxa⟩ := List.mem_flatMap.1 hx'
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hxa
    exact Subgroup.mul_mem _ (pr3_mem hx a) (pr3_mem hy b)) (by rw [hS]; rfl)
  intro s hs
  obtain ⟨a, -, hsa⟩ := List.mem_flatMap.1 (hall s hs)
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hsa
  exact ⟨a, b, rfl⟩

theorem decE_of (hx : ∀ i, xs i ∈ QS.originalSubgroup)
    (hy : ∀ j, ys j ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm))
    (hdec : ∀ s ∈ QS.originalSubgroup, ∃ a b : Fin 3 → ZMod 2, s = pr3 xs a * pr3 ys b)
    (hnc : ncOK = true) :
    ∀ t ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm),
      ∃ b : Fin 3 → ZMod 2, t = pr3 ys b := by
  intro t ht
  obtain ⟨a, b, rfl⟩ := hdec _ (Subgroup.mem_inf.1 ht).1
  by_cases ha : isZ a = true
  · simp only [isZ, Bool.and_eq_true, beq_iff_eq] at ha
    refine ⟨b, ?_⟩
    simp [pr3, ha.1.1, ha.1.2, ha.2]
  · exfalso
    have hnc' := List.all_eq_true.1 hnc a (allVec3_mem a)
    simp only [Bool.not_eq_true] at ha
    simp only [ha, Bool.false_or] at hnc'
    obtain ⟨i, -, hi⟩ := List.any_eq_true.1 hnc'
    have hcen : pr3 xs a ∈ Subgroup.centralizer (QS.originalSubgroup : Set Pm) := by
      rw [← mul_inv_cancel_right (pr3 xs a) (pr3 ys b)]
      exact (Subgroup.mem_inf.1 (Subgroup.mul_mem _ ht
        (Subgroup.inv_mem _ (pr3_mem hy b)))).2
    have hcomm := Subgroup.mem_centralizer_iff.1 hcen (xs i) (hx i)
    have h1 : eq22C (pr3 xsC a) (xsC i) (xsC i) (pr3 xsC a) = true := by
      rw [eq22C_eq, decide_eq_true_eq]
      apply ev_injective
      rw [ev_mul, ev_mul, ← pr3_xs, ev_xsC]
      exact hcomm.symm
    rw [h1] at hi
    exact absurd hi (by decide)

theorem conj_of {c : CV 65} {M W N : Fin 3 → Fin 3 → ZMod 2} (h : conjOK c M W N = true)
    (hy : ∀ j, ys j ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm)) :
    (∀ i, ∃ w ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm),
      ev c * xs i * (ev c)⁻¹ = pr3 xs (fun k => M k i) * w) ∧
    ∀ j, ev c * ys j * (ev c)⁻¹ = pr3 ys (fun l => N l j) := by
  unfold conjOK at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have h1 := of_eq22C (h.1 i (List.mem_finRange i))
    rw [ev_xsC, ev_mul, ← pr3_xs, ← pr3_ys] at h1
    exact ⟨pr3 ys (W i), pr3_mem hy _, by rw [h1, mul_inv_cancel_right]⟩
  · have h1 := of_eq22C (h.2 j (List.mem_finRange j))
    rw [ev_ysC, ← pr3_ys] at h1
    rw [h1, mul_inv_cancel_right]

theorem sq_of {qv : List (Fin 3 → ZMod 2)} (h : sqOK qv = true) :
    ∀ a, pr3 xs a ^ 2 = pr3 ys (qOf qv a) := by
  intro a
  have h1 := of_eq22C (List.all_eq_true.1 h a (allVec3_mem a))
  rw [ev_one, mul_one, ← pr3_xs, ← pr3_ys] at h1
  rw [pow_two, h1]

theorem invB_of {M N u : Fin 3 → Fin 3 → ZMod 2} (h : InvMat M N u) : invB M N u = true := by
  refine List.all_eq_true.2 fun i _ => List.all_eq_true.2 fun j _ => decide_eq_true ?_
  rw [h i j]
  simp only [s3, Fin.sum_univ_three]

theorem cycB_of {qv : List (Fin 3 → ZMod 2)} {u : Fin 3 → Fin 3 → ZMod 2}
    (h : CycMat (qOf qv) u) : cycB qv u = true := by
  refine List.all_eq_true.2 fun a _ => decide_eq_true ?_
  have := h a
  simpa only [s3, Fin.sum_univ_three] using this

theorem zeroB_sound {u : Fin 3 → Fin 3 → ZMod 2} (h : zeroB u = true) : ∀ i j, u i j = 0 :=
  fun i j => of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h i
    (List.mem_finRange i)) j (List.mem_finRange j))

theorem alg_of {M₁ N₁ M₂ N₂ : Fin 3 → Fin 3 → ZMod 2} {qv : List (Fin 3 → ZMod 2)}
    (h : kAlgB M₁ N₁ M₂ N₂ qv = true) :
    ∀ u : Fin 3 → Fin 3 → ZMod 2, InvMat M₁ N₁ u → InvMat M₂ N₂ u → CycMat (qOf qv) u →
      ∀ i j, u i j = 0 := by
  intro u hu1 hu2 hu3
  have h1 := List.all_eq_true.1 h u (allU_mem u)
  rw [invB_of hu1, invB_of hu2, cycB_of hu3] at h1
  exact zeroB_sound (by simpa using h1)

theorem mem_St {g : Pm} : g ∈ MulAction.stabilizer Pm cpt ↔ g cpt = cpt := by
  rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]

theorem A_le_normalizer (hP : ValidSchreier QP)
    (hnorm : normCheck QP QA.original.toList pa pb = true) :
    QA.originalSubgroup ≤ Subgroup.normalizer (QP.originalSubgroup : Set Pm) := by
  rw [RawSchreierDatum.originalSubgroup.eq_1 QA, Subgroup.closure_le]
  intro σ hσ
  have hσ' : σ ∈ QA.original.toList := hσ
  have h1 := List.all_eq_true.1 hnorm σ hσ'
  simp only [Bool.and_eq_true] at h1
  have ha : σ * pa * σ⁻¹ ∈ QP.originalSubgroup := (mem_iff_sift QP hP _).2 h1.1
  have hb : σ * pb * σ⁻¹ ∈ QP.originalSubgroup := (mem_iff_sift QP hP _).2 h1.2
  apply mem_normalizer_of_conj_mem
  intro x hx
  have hle : Subgroup.closure ({pa, pb} : Set Pm) ≤
      QP.originalSubgroup.comap (MulAut.conj σ).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with hy | hy
    · rw [hy]
      exact ha
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hb
  rw [QP_closure] at hx
  exact hle hx

theorem hfin_of (hP : ValidSchreier QP) (hPc : QP.orderCertificate = 29120)
    (hA : ValidSchreier QA) (hAc : QA.orderCertificate = 87360)
    (hnorm : normCheck QP QA.original.toList pa pb = true)
    (hsch : schP QS = true) (hord : orderV QS = 64)
    (hxs : (List.finRange 3).all (fun i => siftC QS (xsC i) 0) = true)
    (hys : (List.finRange 3).all (fun j => siftC QS (ysC j) 0) = true)
    (hsyP : syC.all (fun c => siftC QP c 0) = true)
    (horb : orbOK 37 40 = true) (hpa : img 65 (cOf pa).1 37 = 40)
    (hcent : ysCentOK = true) (hcomm : commOK = true) (hnc : ncOK = true)
    (hdec : decOK = true) (htN : normSOK (cOf tt) = true) (ht7 : powOneC (cOf tt) 7 = true)
    (ht1 : powOneC (cOf tt) 1 = false) (htP : siftC QP (cOf tt) 0 = true)
    (htfix : img 65 (cOf tt).1 37 = 37) (hsfix : img 65 sig0.1 37 = 37)
    {M₁ W₁ N₁ M₂ W₂ N₂ : Fin 3 → Fin 3 → ZMod 2} {qv : List (Fin 3 → ZMod 2)}
    (hc₁ : conjOK (cOf tt) M₁ W₁ N₁ = true) (hc₂ : conjOK sig0 M₂ W₂ N₂ = true)
    (hsq : sqOK qv = true) (halg : kAlgB M₁ N₁ M₂ N₂ qv = true)
    (κ : Pm → Pm → ZMod 2)
    (h1 : ∀ x ∈ QS.originalSubgroup, ∀ x' ∈ QS.originalSubgroup,
      ∀ y ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm),
        κ (x * x') y = κ x y + κ x' y)
    (h2 : ∀ x ∈ QS.originalSubgroup,
      ∀ y ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm),
      ∀ y' ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm),
        κ x (y * y') = κ x y + κ x y')
    (h3 : ∀ w ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm),
      ∀ y ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm),
        κ w y = 0)
    (h5 : ∀ x ∈ QS.originalSubgroup, κ x (x ^ 2) = 0)
    (h4t : ∀ s ∈ QS.originalSubgroup,
      ∀ t ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm),
        κ (tt * s * tt⁻¹) (tt * t * tt⁻¹) = κ s t)
    (σ : Pm) (hσA : σ ∈ QA.originalSubgroup) (hσfix : σ cpt = cpt)
    (hσP : σ ∉ QP.originalSubgroup)
    (h4σ : ∀ s ∈ QS.originalSubgroup,
      ∀ t ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm),
        κ (σ * s * σ⁻¹) (σ * t * σ⁻¹) = κ s t) :
    ∀ s ∈ QS.originalSubgroup,
      ∀ t ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm),
        κ s t = 0 := by
  have hQS := QS_valid_of hsch
  have hS64 := card_S_of hQS hord
  have hSP := S_le_P hP hsyP
  have hSfix := S_fix_of hQS horb
  have hxS := xs_S hQS hxs
  have hyE := ys_mem_of hQS hys hcent
  have hdecS := dec_of hQS hS64 hxS (fun j => (Subgroup.mem_inf.1 (hyE j)).1) hdec
  have httP : tt ∈ QP.originalSubgroup := by
    rw [← ev_cOf tt]
    exact mem_of_siftC hP htP
  have httfix : tt cpt = cpt := Fin.ext (by rw [← ev_cOf tt, ev_apply]; exact htfix)
  have ht7' : tt ^ 7 = 1 := by
    have h0 := of_decide_eq_true ((pow_fast _ _).trans ht7)
    rw [← ev_cOf tt, ev_pow', h0, ev_one]
  have ht1' : tt ≠ 1 := by
    intro h
    have h0 : decide ((cOf tt) ^ 1 = 1) = true := by
      rw [decide_eq_true_eq, pow_one]
      apply ev_injective
      rw [ev_cOf, ev_one, h]
    rw [pow_fast, ht1] at h0
    exact absurd h0 (by decide)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hto : orderOf tt = 7 := orderOf_eq_prime ht7' ht1'
  have httS : ∀ s ∈ QS.originalSubgroup, tt * s * tt⁻¹ ∈ QS.originalSubgroup := by
    have hle : QS.originalSubgroup ≤ QS.originalSubgroup.comap (MulAut.conj tt).toMonoidHom := by
      conv_lhs => rw [S_closure]
      rw [Subgroup.closure_le]
      intro a ha
      have h0 := mem_of_siftC hQS (List.all_eq_true.1 htN _ (mem_syC ha))
      simp only [ev_mul, ev_inv, ev_cOf] at h0
      exact Subgroup.mem_comap.2 (by simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply])
    intro s hs
    have h0 := Subgroup.mem_comap.1 (hle hs)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h0
  have hpaP : pa ∈ QP.originalSubgroup := by
    rw [QP_closure]
    exact Subgroup.subset_closure (by simp)
  have hpa' : pa cpt = 40 := Fin.ext (by rw [← ev_cOf pa, ev_apply]; exact hpa)
  have htr : ∀ i, ∃ g ∈ QP.originalSubgroup, g cpt = i := by
    intro i
    by_cases hi : i = cpt
    · exact ⟨1, Subgroup.one_mem _, by rw [hi]; rfl⟩
    · obtain ⟨s, hs, hsi⟩ := S_orbit_of hQS horb i hi
      exact ⟨s * pa, Subgroup.mul_mem _ (hSP hs) hpaP, by rw [Equiv.Perm.mul_apply, hpa', hsi]⟩
  have htrA : ∀ i, ∃ g ∈ QA.originalSubgroup, g cpt = i := fun i => by
    obtain ⟨g, hg, h⟩ := htr i
    exact ⟨g, P_le_A hg, h⟩
  have hB : Nat.card ↥(QP.originalSubgroup ⊓ MulAction.stabilizer Pm cpt) = 448 := by
    have h0 := card_stab_mul _ cpt htr
    rw [Fintype.card_fin, card_group QP hP, hPc] at h0
    omega
  have hA0 : Nat.card ↥(QA.originalSubgroup ⊓ MulAction.stabilizer Pm cpt) = 1344 := by
    have h0 := card_stab_mul _ cpt htrA
    rw [Fintype.card_fin, card_group QA hA, hAc] at h0
    omega
  have hSB : QS.originalSubgroup ≤ QP.originalSubgroup ⊓ MulAction.stabilizer Pm cpt :=
    le_inf hSP fun s hs => mem_St.2 (hSfix s hs)
  have htB : tt ∈ QP.originalSubgroup ⊓ MulAction.stabilizer Pm cpt :=
    Subgroup.mem_inf.2 ⟨httP, mem_St.2 httfix⟩
  have hBN : QP.originalSubgroup ⊓ MulAction.stabilizer Pm cpt ≤
      Subgroup.normalizer (QS.originalSubgroup : Set Pm) := by
    have h64 : 64 ∣ Nat.card ↥(QP.originalSubgroup ⊓ MulAction.stabilizer Pm cpt ⊓
        Subgroup.normalizer (QS.originalSubgroup : Set Pm)) :=
      hS64 ▸ Subgroup.card_dvd_of_le (le_inf hSB (Subgroup.le_normalizer))
    exact (le_of_card448 inf_le_left hB h64 (Subgroup.mem_inf.2 ⟨htB,
      mem_normalizer_of_conj_mem _ tt httS⟩) hto).trans inf_le_right
  have hN : ∀ g ∈ QA.originalSubgroup ⊓ MulAction.stabilizer Pm cpt,
      ∀ s ∈ QS.originalSubgroup, g * s * g⁻¹ ∈ QS.originalSubgroup := by
    intro g hg
    obtain ⟨hgA, hgS⟩ := Subgroup.mem_inf.1 hg
    refine conj_mem_of_normal hSB hBN hS64 hB g fun b hb => ?_
    obtain ⟨hbP, hbS⟩ := Subgroup.mem_inf.1 hb
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (A_le_normalizer hP hnorm hgA) b).1
      hbP, Subgroup.mul_mem _ (Subgroup.mul_mem _ hgS hbS) (Subgroup.inv_mem _ hgS)⟩
  have hNE : ∀ g ∈ QA.originalSubgroup ⊓ MulAction.stabilizer Pm cpt,
      ∀ t ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm),
        g * t * g⁻¹ ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm) :=
    fun g hg => conj_mem_center g (hN g hg) (hN g⁻¹ (Subgroup.inv_mem _ hg))
  have hinvS : ∀ g ∈ QS.originalSubgroup, ∀ s ∈ QS.originalSubgroup,
      ∀ t ∈ QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm),
        κ (g * s * g⁻¹) (g * t * g⁻¹) = κ s t := by
    intro g hg s hs t ht
    have hgt : g * t * g⁻¹ = t := by
      rw [Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 ht).2 g hg, mul_inv_cancel_right]
    have hc : s⁻¹ * g * s⁻¹⁻¹ * g⁻¹ ∈
        QS.originalSubgroup ⊓ Subgroup.centralizer (QS.originalSubgroup : Set Pm) :=
      Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ hs) hg) (Subgroup.inv_mem _ (Subgroup.inv_mem _ hs)))
        (Subgroup.inv_mem _ hg), comm_S hcomm _ (Subgroup.inv_mem _ hs) _ hg⟩
    have e : g * s * g⁻¹ = s * (s⁻¹ * g * s⁻¹⁻¹ * g⁻¹) := by group
    rw [hgt, e, h1 _ hs _ (Subgroup.mem_inf.1 hc).1 _ ht, h3 _ hc _ ht, add_zero]
  have hσ0 : ev sig0 ∈ QA.originalSubgroup ⊓ MulAction.stabilizer Pm cpt := by
    refine Subgroup.mem_inf.2 ⟨?_, mem_St.2 (Fin.ext (by rw [ev_apply]; exact hsfix))⟩
    have hmem : ∀ g ∈ [pa, pb, sg0], g ∈ QA.originalSubgroup := fun g hg => by
      rw [A_closure]
      exact Subgroup.subset_closure hg
    simp only [sig0, wP, ev_mul, ev_inv, ev_cOf]
    have hpa := hmem pa (by simp)
    have hpb := hmem pb (by simp)
    have hsg := hmem sg0 (by simp)
    have hw : pa * pb * pa ∈ QA.originalSubgroup :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hpa hpb) hpa
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw hsg) (Subgroup.inv_mem _ hw)
  have hinv := inv_all κ hSB (inf_le_inf_right _ P_le_A) hS64 hB hA0 hN hNE hinvS htB hto h4t
    (Subgroup.mem_inf.2 ⟨hσA, mem_St.2 hσfix⟩) (fun h => hσP (Subgroup.mem_inf.1 h).1) h4σ
  obtain ⟨hM₁, hN₁⟩ := conj_of hc₁ hyE
  obtain ⟨hM₂, hN₂⟩ := conj_of hc₂ hyE
  rw [ev_cOf] at hM₁ hN₁
  exact kappa_vanish inf_le_left h1 h2 h3 hxS hyE
    (fun s hs => by
      obtain ⟨a, b, rfl⟩ := hdecS s hs
      exact ⟨a, pr3 ys b, pr3_mem hyE b, rfl⟩)
    (decE_of hxS hyE hdecS hnc) tt (ev sig0) h4t (hinv _ hσ0) h5 M₁ N₁ M₂ N₂ hM₁ hN₁ hM₂ hN₂
    (qOf qv) (sq_of hsq) (alg_of halg)

end CFSG.Certificates.Kernel.PkCV.KGrp.K5129

end
