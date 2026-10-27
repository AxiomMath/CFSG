module

public import CFSG.CGT.PushingUpLit.J42.S5ExtIface
public import CFSG.CGT.PushingUpLit.J42.S5Rank

public section

namespace CFSG.CGT.PushingUpLit.SolK

theorem s5ext_exists_step {K : Type*} [Group K] [Finite K] {H B : Subgroup K}
    (hH : IsPGroup 2 H) (hBH : B < H) :
    ∃ g ∈ H, g ∉ B ∧ g * g ∈ B ∧ g ∈ Subgroup.normalizer (B : Set K) := by
  have hnil : Group.IsNilpotent ↥H := hH.isNilpotent
  have hlt : B.subgroupOf H < ⊤ :=
    lt_top_iff_ne_top.2 fun htop => hBH.not_ge (Subgroup.subgroupOf_eq_top.1 htop)
  obtain ⟨x, hxN, hxB⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (B.subgroupOf H) hlt)
  rw [← Subgroup.subgroupOf_normalizer_eq hBH.le, Subgroup.mem_subgroupOf] at hxN
  rw [Subgroup.mem_subgroupOf] at hxB
  obtain ⟨k, hk⟩ := hH x
  have hk' : (x : K) ^ 2 ^ k = 1 := by
    rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]
  have hex : ∃ j, (x : K) ^ 2 ^ (j + 1) ∈ B :=
    ⟨k, by rw [pow_succ, pow_mul, hk', one_pow]; exact B.one_mem⟩
  classical
  obtain ⟨j, hj, hjmin⟩ :
      ∃ j, (x : K) ^ 2 ^ (j + 1) ∈ B ∧ ∀ j' < j, (x : K) ^ 2 ^ (j' + 1) ∉ B :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j' hj' => Nat.find_min hex hj'⟩
  refine ⟨(x : K) ^ 2 ^ j, H.pow_mem x.2 _, ?_, ?_, Subgroup.pow_mem _ hxN _⟩
  · cases j with
    | zero => simpa using hxB
    | succ j => exact hjmin j (Nat.lt_succ_self j)
  · rwa [← pow_add, ← two_mul, ← pow_succ']

theorem s5ext_exists_adjoin {K : Type*} [Group K] {B : Subgroup K} {g : K} (hgg : g * g ∈ B)
    (hgN : g ∈ Subgroup.normalizer (B : Set K)) :
    ∃ B' : Subgroup K, ∀ x, x ∈ B' ↔ x ∈ B ∨ ∃ b ∈ B, x = g * b := by
  have hc : ∀ b ∈ B, g⁻¹ * b * g ∈ B := fun b hb =>
    (Subgroup.mem_normalizer_iff''.1 hgN b).1 hb
  refine ⟨{ carrier := {x | x ∈ B ∨ ∃ b ∈ B, x = g * b}
            one_mem' := Or.inl B.one_mem
            mul_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x y (hx | ⟨b, hb, rfl⟩) (hy | ⟨b', hb', rfl⟩)
    · exact Or.inl (B.mul_mem hx hy)
    · exact Or.inr ⟨g⁻¹ * x * g * b', B.mul_mem (hc x hx) hb', by group⟩
    · exact Or.inr ⟨b * y, B.mul_mem hb hy, by group⟩
    · refine Or.inl ?_
      rw [show g * b * (g * b') = g * g * (g⁻¹ * b * g) * b' by group]
      exact B.mul_mem (B.mul_mem hgg (hc b hb)) hb'
  · rintro x (hx | ⟨b, hb, rfl⟩)
    · exact Or.inl (B.inv_mem hx)
    · exact Or.inr ⟨g⁻¹ * b⁻¹ * g * (g * g)⁻¹,
        B.mul_mem (hc _ (B.inv_mem hb)) (B.inv_mem hgg), by group⟩

theorem s5ext_incat_congr {I : S5Iface} {p q : ℕ → Prop} (hp : I.InCat p)
    (h : ∀ e, p e ↔ q e) : I.InCat q := by
  have : p = q := funext fun e => propext (h e)
  exact this ▸ hp

theorem s5ext_chain (I : S5Iface) {K : Type*} [Group K] [Finite K] (D : ExtraData K)
    (R : S5Rho D I) {H : Subgroup K} (hH : IsPGroup 2 H) :
    ∀ n : ℕ, ∀ B : Subgroup K, B ≤ H → D.nf 4 ∈ B → Nat.card H - Nat.card B = n →
      I.InCat (fun e => ∃ h ∈ B, R.rho h = e) → I.InCat (fun e => ∃ h ∈ H, R.rho h = e) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B hBH hzB hn hB
    rcases eq_or_lt_of_le hBH with rfl | hlt
    · exact hB
    obtain ⟨g, hgH, hgB, hgg, hgN⟩ := s5ext_exists_step hH hlt
    obtain ⟨B', hB'⟩ := s5ext_exists_adjoin hgg hgN
    have hBB' : B ≤ B' := fun x hx => (hB' x).2 (Or.inl hx)
    have hB'H : B' ≤ H := fun x hx => by
      rcases (hB' x).1 hx with hx | ⟨b, hb, rfl⟩
      · exact hBH hx
      · exact H.mul_mem hgH (hBH hb)
    have hgB' : g ∈ B' := (hB' g).2 (Or.inr ⟨1, B.one_mem, (mul_one g).symm⟩)
    have hcard : Nat.card B < Nat.card B' :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hBB' fun h => hgB (by rw [h]; exact hgB'))
    have hcard' : Nat.card B' ≤ Nat.card H := Subgroup.card_le_of_le hB'H
    have h1 : ¬ ∃ h ∈ B, R.rho h = R.rho g := by
      rintro ⟨b, hb, hbg⟩
      rcases R.rho_ker b g hbg with h | h <;> rw [h] at hgB
      · exact hgB hb
      · exact hgB (B.mul_mem hb hzB)
    have h2 : ∃ h ∈ B, R.rho h = I.cm (R.rho g) (R.rho g) := ⟨g * g, hgg, R.rho_mul g g⟩
    have h3 : ∀ c, c < I.N → (∃ h ∈ B, R.rho h = c) →
        ∃ h ∈ B, R.rho h = I.cm (I.cm (R.rho g) c) (I.inv (R.rho g)) := by
      rintro c - ⟨b, hb, rfl⟩
      refine ⟨g * b * g⁻¹, (Subgroup.mem_normalizer_iff.1 hgN b).1 hb, ?_⟩
      rw [R.rho_mul, R.rho_mul, R.rho_inv]
    refine ih (Nat.card H - Nat.card B') (by omega) B' hB'H (hBB' hzB) rfl
      (s5ext_incat_congr (I.cat_step _ hB (R.rho g) (R.rho_lt g) h1 h2 h3) fun e => ?_)
    constructor
    · rintro (⟨h, hh, rfl⟩ | ⟨c, -, ⟨b, hb, rfl⟩, rfl⟩)
      · exact ⟨h, hBB' hh, rfl⟩
      · exact ⟨g * b, (hB' _).2 (Or.inr ⟨b, hb, rfl⟩), R.rho_mul g b⟩
    · rintro ⟨h, hh, rfl⟩
      rcases (hB' h).1 hh with hh | ⟨b, hb, rfl⟩
      · exact Or.inl ⟨h, hh, rfl⟩
      · exact Or.inr ⟨R.rho b, R.rho_lt b, ⟨b, hb, rfl⟩, (R.rho_mul g b).symm⟩

theorem s5ext_incat (I : S5Iface) {K : Type*} [Group K] [Finite K] (D : ExtraData K)
    (R : S5Rho D I) {H : Subgroup K} (hH : IsPGroup 2 H) (hz : D.nf 4 ∈ H) :
    I.InCat (fun e => ∃ h ∈ H, R.rho h = e) := by
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Subgroup K, ∀ x, x ∈ B₀ ↔ x = 1 ∨ x = D.nf 4 := by
    have hzi : (D.nf 4)⁻¹ = D.nf 4 := inv_eq_of_mul_eq_one_right R.z_sq
    refine ⟨{ carrier := {x | x = 1 ∨ x = D.nf 4}
              one_mem' := Or.inl rfl
              mul_mem' := ?_
              inv_mem' := ?_ }, fun x => Iff.rfl⟩
    · rintro x y (rfl | rfl) (rfl | rfl)
      · exact Or.inl (mul_one 1)
      · exact Or.inr (one_mul _)
      · exact Or.inr (mul_one _)
      · exact Or.inl R.z_sq
    · rintro x (rfl | rfl)
      · exact Or.inl inv_one
      · exact Or.inr hzi
  have hB₀H : B₀ ≤ H := fun x hx => by
    rcases (hB₀ x).1 hx with rfl | rfl
    · exact H.one_mem
    · exact hz
  refine s5ext_chain I D R hH _ B₀ hB₀H ((hB₀ _).2 (Or.inr rfl)) rfl
    (s5ext_incat_congr I.cat_one fun e => ?_)
  constructor
  · rintro rfl
    exact ⟨1, (hB₀ 1).2 (Or.inl rfl), R.rho_one⟩
  · rintro ⟨h, hh, rfl⟩
    rcases (hB₀ h).1 hh with rfl | rfl
    · exact R.rho_one
    · exact R.rho_z

theorem s5ext_tab_inv {I : S5Iface} {K : Type*} [Group K] {D : ExtraData K} (R : S5Rho D I)
    (k : K) (w : Fin 32) : I.tab (R.rho k⁻¹) (I.tab (R.rho k) w) = w := by
  rw [← I.cm_tab _ _ (R.rho_lt _) (R.rho_lt _), ← R.rho_mul, inv_mul_cancel, R.rho_one,
    I.ide_tab]

theorem s5ext_gen_of_incat (I : S5Iface) {K : Type*} [Group K] [Finite K] (D : ExtraData K)
    (R : S5Rho D I) {H : Subgroup K} (hH : IsPGroup 2 H) (hz : D.nf 4 ∈ H) {S : ℕ → Prop}
    (hS : ∀ e, S e ↔ ∃ h ∈ H, R.rho h = e) (hcat : I.InCat S) :
    ∃ s : Finset K, s.card ≤ 4 ∧ Subgroup.closure (s : Set K) = H := by
  classical
  obtain ⟨as, ts, hlen, has, hts, hP, hQ⟩ := I.cat_wit S hcat
  have hlift : ∀ a : ℕ, ∃ l : K, S a → l ∈ H ∧ R.rho l = a := fun a => by
    by_cases ha : S a
    · obtain ⟨h, hh, rfl⟩ := (hS a).1 ha
      exact ⟨h, fun _ => ⟨hh, rfl⟩⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose ℓ hℓ using hlift
  obtain ⟨s, hscard, hsmem⟩ :
      ∃ s : Finset K, s.card ≤ as.length ∧ ∀ x, x ∈ s ↔ ∃ a ∈ as, ℓ a = x :=
    ⟨(as.map ℓ).toFinset, (List.toFinset_card_le _).trans (by simp), fun x => by simp⟩
  obtain ⟨t, htcard, htmem⟩ :
      ∃ t : Finset K, t.card ≤ ts.length ∧ ∀ x, x ∈ t ↔ ∃ i ∈ ts, D.nf i = x :=
    ⟨(ts.map D.nf).toFinset, (List.toFinset_card_le _).trans (by simp), fun x => by simp⟩
  obtain ⟨L, hL, hLle⟩ : ∃ L : Subgroup K, (∀ i, S (I.ci i) → D.nf i ∈ L) ∧
      ∀ N : Subgroup K, (∀ i, S (I.ci i) → D.nf i ∈ N) → L ≤ N := by
    refine ⟨Subgroup.closure {x | ∃ i, S (I.ci i) ∧ D.nf i = x},
      fun i hi => Subgroup.subset_closure ⟨i, hi, rfl⟩, fun N hN => ?_⟩
    rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hN i hi
  have hzL : D.nf 4 ∈ L := hL 4 ((hS _).2 ⟨D.nf 4, hz, R.rho_nf 4⟩)
  have hfib : ∀ i, S (I.ci i) → ∀ h, R.rho h = I.ci i → h ∈ L := by
    intro i hi h hρ
    rcases R.rho_ker (D.nf i) h ((R.rho_nf i).trans hρ.symm) with he | he <;> rw [he]
    · exact hL i hi
    · exact L.mul_mem (hL i hi) hzL
  have hLH : L ≤ H := hLle H fun i hi => by
    obtain ⟨h, hh, hρ⟩ := (hS _).1 hi
    rcases R.rho_ker h (D.nf i) (hρ.trans (R.rho_nf i).symm) with he | he <;> rw [he]
    · exact hh
    · exact H.mul_mem hh hz
  have hs : (s : Set K) ⊆ H := fun x hx => by
    obtain ⟨a, ha, rfl⟩ := (hsmem x).1 hx
    exact (hℓ a (has a ha).2).1
  have ht : (t : Set K) ⊆ L := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := (htmem x).1 hx
    exact hL i (hts i hi)
  have hsL : Subgroup.closure (s : Set K) ⊔ L = H := by
    refine le_antisymm (sup_le ((Subgroup.closure_le H).2 hs) hLH) fun h hh => ?_
    refine hP (fun x => ∀ h ∈ H, R.rho h = x → h ∈ Subgroup.closure (s : Set K) ⊔ L) ?_ ?_
      (R.rho h) (R.rho_lt h) ((hS _).2 ⟨h, hh, rfl⟩) h hh rfl
    · intro i hi h' _ hρ
      exact Subgroup.mem_sup_right (hfib i hi h' hρ)
    · intro a ha x hx hPx h' hh' hρ
      obtain ⟨hla, hρa⟩ := hℓ a (has a ha).2
      have hinv := s5ext_tab_inv R (ℓ a)
      rw [hρa] at hinv
      have hrho : R.rho ((ℓ a)⁻¹ * h') = x := by
        refine I.tab_inj _ _ (R.rho_lt _) hx (funext fun y => ?_)
        rw [R.rho_mul, I.cm_tab _ _ (R.rho_lt _) (R.rho_lt _), hρ,
          I.cm_tab _ _ (has a ha).1 hx, hinv]
      have hls : ℓ a ∈ Subgroup.closure (s : Set K) ⊔ L :=
        Subgroup.mem_sup_left (Subgroup.subset_closure ((hsmem _).2 ⟨a, ha, rfl⟩))
      simpa using Subgroup.mul_mem _ hls (hPx _ (H.mul_mem (H.inv_mem hla) hh') hrho)
  have htL : ∀ N : Subgroup K, N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) →
      (t : Set K) ⊆ N → L ≤ N := by
    intro N _ hinv htN
    refine hLle N fun i hi => hQ (fun i => D.nf i ∈ N) ?_ ?_ i hi
    · intro α _ hα t' ht'
      obtain ⟨h, hh, rfl⟩ := (hS α).1 hα
      show D.nf (I.tab (R.rho h) t') ∈ N
      rw [R.rho_conj]
      exact hinv h hh _ (htN ((htmem _).2 ⟨t', ht', rfl⟩))
    · intro x y hx hy
      show D.nf (extraMulFin x y) ∈ N
      rw [← D.nf_mul]
      exact N.mul_mem hx hy
  obtain ⟨r, hr, hcl⟩ := exists_card_le_of_normalClosure hH hLH hs ht hsL htL
  exact ⟨r, by omega, hcl⟩

theorem s5ext_gen4_core (I : S5Iface) {K : Type*} [Group K] [Finite K] (D : ExtraData K)
    (R : S5Rho D I) (H : Subgroup K) (hH : IsPGroup 2 H) (hz : D.nf 4 ∈ H) :
    ∃ s : Finset K, s.card ≤ 4 ∧ Subgroup.closure (s : Set K) = H :=
  s5ext_gen_of_incat I D R hH hz (fun _ => Iff.rfl) (s5ext_incat I D R hH hz)

end CFSG.CGT.PushingUpLit.SolK
