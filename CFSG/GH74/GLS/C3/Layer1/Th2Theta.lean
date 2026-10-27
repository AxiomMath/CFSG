module

public import CFSG.GH74.GLS.C3.Layer1.Th2SigStmt
public import CFSG.GH74.GLS.C3.Layer1.BackConj

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

abbrev cj (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem cj_cj_inv (g : G) (H : Subgroup G) : cj g⁻¹ (cj g H) = H := by
  unfold cj
  rw [Subgroup.map_map]
  have : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) = MonoidHom.id G := by
    ext x; simp [MulAut.conj_apply, mul_assoc]
  rw [this, Subgroup.map_id]

theorem cj_inv_cj (g : G) (H : Subgroup G) : cj g (cj g⁻¹ H) = H := by
  simpa using cj_cj_inv g⁻¹ H

theorem mem_cj_iff (g : G) (H : Subgroup G) (b : G) : b ∈ cj g H ↔ g⁻¹ * b * g ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro h
    exact ⟨g⁻¹ * b * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem cj_le_iff {H K : Subgroup G} (g : G) : cj g H ≤ K ↔ H ≤ cj g⁻¹ K := by
  constructor
  · intro h x hx
    rw [mem_cj_iff]
    have hx' : g * x * g⁻¹ ∈ cj g H := (mem_cj_iff g H _).2 (by simpa [mul_assoc] using hx)
    simpa using h hx'
  · intro h x hx
    rw [mem_cj_iff] at hx
    have := h hx
    rw [mem_cj_iff] at this
    simpa [mul_assoc] using this

theorem cj_eq_of_mem_normalizer {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) :
    cj g H = H := by
  ext x
  rw [mem_cj_iff]
  have h1 := Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * x * g)
  rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
  exact h1

theorem mem_normalizer_of_cj_eq {H : Subgroup G} {g : G} (h : cj g H = H) :
    g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := mem_cj_iff g H (g * x * g⁻¹)
  rw [h, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1
  exact h1.symm

theorem pRank_two_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) : CFSG.pRank 2 A = CFSG.pRank 2 B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv one_lt_two e

theorem pRank_cj [Finite G] (g : G) (H : Subgroup G) : CFSG.pRank 2 ↥(cj g H) = CFSG.pRank 2 ↥H :=
  (pRank_two_eq_of_mulEquiv ((MulAut.conj g).subgroupMap H)).symm

theorem isElementaryAbelian_cj (g : G) {H : Subgroup G} (h : CFSG.IsElementaryAbelian 2 ↥H) :
    CFSG.IsElementaryAbelian 2 ↥(cj g H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h
  exact CFSG.IsElementaryAbelian.map (p := 2) (A := H) (MulAut.conj g).toMonoidHom

theorem isE_cj [Finite G] {n : ℕ} {X B : Subgroup G} (h : IsE n X B) (g : G) :
    IsE n (cj g X) (cj g B) :=
  ⟨Subgroup.map_mono h.1, isElementaryAbelian_cj g h.2.1, by rw [pRank_cj]; exact h.2.2⟩

theorem pPrimeCoreOf_cj (g : G) (K : Subgroup G) :
    pPrimeCoreOf 2 (cj g K) = cj g (pPrimeCoreOf 2 K) := by
  show pPrimeCoreOf 2 (K.map (MulAut.conj g).toMonoidHom) =
    (pPrimeCoreOf 2 K).map (MulAut.conj g).toMonoidHom
  unfold pPrimeCoreOf
  let ψ : ↥K ≃* ↥(K.map (MulAut.conj g).toMonoidHom) := (MulAut.conj g).subgroupMap K
  rw [← CFSG.pPrimeCore_map_iso 2 ψ, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem cj_centralizer_singleton (g b : G) :
    cj g (centralizer ({b} : Set G)) = centralizer ({g * b * g⁻¹} : Set G) := by
  ext c
  rw [mem_cj_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc c * (g * b * g⁻¹) = g * ((g⁻¹ * c * g) * b) * g⁻¹ := by group
      _ = g * (b * (g⁻¹ * c * g)) * g⁻¹ := by rw [h]
      _ = g * b * g⁻¹ * c := by group
  · intro h
    have h2 : c * (g * b * g⁻¹) = g * b * g⁻¹ * c := h
    calc g⁻¹ * c * g * b = g⁻¹ * (c * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹ * c) * g := by rw [h2]
      _ = b * (g⁻¹ * c * g) := by group

theorem mem_AG_iff {D : Subgroup G} {x : G} :
    x ∈ AG D ↔ ∀ b ∈ D, b ≠ 1 → x ∈ pPrimeCoreOf 2 (centralizer ({b} : Set G)) := by
  unfold AG
  simp only [Subgroup.mem_iInf]
  constructor
  · intro h b hb hb1
    exact h b ⟨hb, hb1⟩
  · intro h b hb
    exact h b hb.1 hb.2

theorem AG_cj (g : G) (D : Subgroup G) : AG (cj g D) = cj g (AG D) := by
  ext x
  rw [mem_AG_iff, mem_cj_iff, mem_AG_iff]
  constructor
  · intro h b hb hb1
    have hb' : g * b * g⁻¹ ∈ cj g D := (mem_cj_iff g D _).2 (by simpa [mul_assoc] using hb)
    have hne : g * b * g⁻¹ ≠ 1 := by
      intro h1
      apply hb1
      have : b = g⁻¹ * (g * b * g⁻¹) * g := by group
      rw [this, h1]; group
    have := h _ hb' hne
    rw [← cj_centralizer_singleton, pPrimeCoreOf_cj, mem_cj_iff] at this
    exact this
  · intro h b hb hb1
    rw [mem_cj_iff] at hb
    have hne : g⁻¹ * b * g ≠ 1 := by
      intro h1
      apply hb1
      have : b = g * (g⁻¹ * b * g) * g⁻¹ := by group
      rw [this, h1]; group
    have := h _ hb hne
    have hb2 : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
    rw [← hb2, ← cj_centralizer_singleton, pPrimeCoreOf_cj, mem_cj_iff]
    simpa using this

theorem thetaK_cj [Finite G] (k : ℕ) (g : G) (B : Subgroup G) :
    thetaK k (cj g B) = cj g (thetaK k B) := by
  apply le_antisymm
  · refine iSup₂_le fun D hD => ?_
    have hD' : IsE k B (cj g⁻¹ D) := by
      have := isE_cj hD g⁻¹
      rwa [cj_cj_inv] at this
    have h1 : AG D = cj g (AG (cj g⁻¹ D)) := by rw [← AG_cj, cj_inv_cj]
    rw [h1]
    exact Subgroup.map_mono (le_iSup₂_of_le (cj g⁻¹ D) hD' le_rfl)
  · rw [cj_le_iff]
    refine iSup₂_le fun D hD => ?_
    rw [← cj_le_iff, ← AG_cj]
    exact le_iSup₂_of_le (cj g D) (isE_cj hD g) le_rfl

theorem thetaHalf_cj [Finite G] (k : ℕ) (g : G) (B : Subgroup G) :
    thetaHalf k (cj g B) = cj g (thetaHalf k B) := by
  have hmap : ∀ H : Subgroup G, cj g H = H.map (MulAut.conj g).toMonoidHom := fun _ => rfl
  apply le_antisymm
  · refine sup_le (iSup₂_le fun D hD => ?_) ?_
    · have hD' : IsE k B (cj g⁻¹ D) := by
        have := isE_cj hD g⁻¹
        rwa [cj_cj_inv] at this
      have h1 : AG D = cj g (AG (cj g⁻¹ D)) := by rw [← AG_cj, cj_inv_cj]
      have h2 : ⁅AG D, cj g B⁆ = cj g ⁅AG (cj g⁻¹ D), B⁆ := by
        rw [h1, hmap, hmap, hmap, Subgroup.map_commutator]
      rw [h2]
      exact Subgroup.map_mono (le_sup_of_le_left (le_iSup₂_of_le (cj g⁻¹ D) hD' le_rfl))
    · rw [AG_cj]; exact Subgroup.map_mono le_sup_right
  · rw [cj_le_iff]
    refine sup_le (iSup₂_le fun D hD => ?_) ?_
    · rw [← cj_le_iff]
      have h2 : cj g ⁅AG D, B⁆ = ⁅AG (cj g D), cj g B⁆ := by
        rw [AG_cj, hmap, hmap, hmap, Subgroup.map_commutator]
      rw [h2]
      exact le_sup_of_le_left (le_iSup₂_of_le (cj g D) (isE_cj hD g) le_rfl)
    · rw [← cj_le_iff, ← AG_cj]
      exact le_sup_right

theorem theta_cj [Finite G] (ℓ : Th2Level) (g : G) (B : Subgroup G) :
    ℓ.theta (cj g B) = cj g (ℓ.theta B) := by
  cases ℓ
  · exact thetaK_cj 1 g B
  · exact thetaHalf_cj 2 g B
  · exact thetaK_cj 3 g B

theorem norm_le_of_theta_eq [Finite G] (ℓ : Th2Level) {A B : Subgroup G}
    (h : ℓ.theta A = ℓ.theta B) {g : G} (hg : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer (ℓ.theta B : Set G) := by
  apply mem_normalizer_of_cj_eq
  rw [← h, ← theta_cj, cj_eq_of_mem_normalizer hg]

theorem exists_mul_of_mem_sup_of_commute {K L : Subgroup G}
    (hcomm : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) {x : G} (hx : x ∈ K ⊔ L) :
    ∃ k ∈ K, ∃ l ∈ L, x = k * l := by
  have comm : ∀ (m : K) (n : L), Commute (K.subtype m) (L.subtype n) :=
    fun m n => hcomm m m.2 n n.2
  have hrange := MonoidHom.noncommCoprod_range K.subtype L.subtype comm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  rw [← hrange] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem isElementaryAbelian_sup {K L : Subgroup G} (hK : CFSG.IsElementaryAbelian 2 ↥K)
    (hL : CFSG.IsElementaryAbelian 2 ↥L) (hcomm : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) :
    CFSG.IsElementaryAbelian 2 ↥(K ⊔ L) := by
  obtain ⟨hKc, hKs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hK
  obtain ⟨hLc, hLs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hL
  refine C3.Layer1.Back.isElementaryAbelian_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · obtain ⟨k, hk, l, hl, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hx
    obtain ⟨k', hk', l', hl', rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hy
    have h1 : Commute k k' := hKc k hk k' hk'
    have h2 : Commute l l' := hLc l hl l' hl'
    have h3 : Commute k l' := hcomm k hk l' hl'
    have h4 : Commute l k' := (hcomm k' hk' l hl).symm
    exact ((h1.mul_right h3).mul_left (h4.mul_right h2)).eq
  · obtain ⟨k, hk, l, hl, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hx
    have hkl : Commute k l := hcomm k hk l hl
    have : (k * l) * (k * l) = (k * k) * (l * l) := by
      calc (k * l) * (k * l) = k * (l * k) * l := by group
        _ = k * (k * l) * l := by rw [← hkl.eq]
        _ = (k * k) * (l * l) := by group
    rw [this, hKs k hk, hLs l hl, one_mul]

theorem exists_elemAbelian_pRank [Finite G] (H : Subgroup G) :
    ∃ E : Subgroup G, E ≤ H ∧ CFSG.IsElementaryAbelian 2 ↥E ∧
      CFSG.pRank 2 ↥E = CFSG.pRank 2 ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Set ℕ := {r | ∃ A : Subgroup ↥H, CFSG.IsElementaryAbelian 2 ↥A ∧ Nat.card A = 2 ^ r}
    with hS
  have hbot : CFSG.IsElementaryAbelian 2 ↥(⊥ : Subgroup ↥H) :=
    C3.Layer1.Back.isElementaryAbelian_of_forall (fun u hu v hv => by
        simp [Subgroup.mem_bot.1 hu, Subgroup.mem_bot.1 hv])
      (fun u hu => by simp [Subgroup.mem_bot.1 hu])
  have hne : S.Nonempty := ⟨0, ⊥, hbot, by simp⟩
  have hbdd : BddAbove S := by
    refine ⟨Nat.card H, ?_⟩
    rintro r ⟨A, -, hA⟩
    calc r ≤ 2 ^ r := (Nat.lt_two_pow_self).le
      _ = Nat.card A := hA.symm
      _ ≤ Nat.card H := Subgroup.card_le_card_group A
  obtain ⟨A, hAel, hAcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨A.map H.subtype, Subgroup.map_subtype_le A, ?_, ?_⟩
  · have := hAel
    exact CFSG.IsElementaryAbelian.map (p := 2) (A := A) H.subtype
  · have hcard : Nat.card ↥(A.map H.subtype) = 2 ^ CFSG.pRank 2 ↥H := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact hAcard
    have hel : CFSG.IsElementaryAbelian 2 ↥(A.map H.subtype) := by
      have := hAel
      exact CFSG.IsElementaryAbelian.map (p := 2) (A := A) H.subtype
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hel] at hcard
    exact Nat.pow_right_injective le_rfl hcard

theorem exists_maximal_elemAbelian [Finite G] {X W : Subgroup G} (hWX : W ≤ X)
    (hW : CFSG.IsElementaryAbelian 2 ↥W) : ∃ B₀ : Subgroup G, W ≤ B₀ ∧ IsS X B₀ := by
  let s : Set (Subgroup G) := {B | W ≤ B ∧ B ≤ X ∧ CFSG.IsElementaryAbelian 2 ↥B}
  have hne : s.Nonempty := ⟨W, le_rfl, hWX, hW⟩
  obtain ⟨B₀, ⟨hWB, hBX, hBel⟩, hmax⟩ :=
    Set.exists_max_image s (fun B => Nat.card B) (Set.toFinite s) hne
  refine ⟨B₀, hWB, hBX, hBel, ?_⟩
  obtain ⟨hBc, hBs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  apply le_antisymm
  · intro b hb
    exact Subgroup.subset_closure ⟨⟨hBX hb, fun c hc => hBc c hc b hb⟩, hBs b hb⟩
  · refine (Subgroup.closure_le B₀).2 ?_
    rintro u ⟨⟨huX, huC⟩, hu2⟩
    have huc : ∀ b ∈ B₀, b * u = u * b := fun b hb => huC b hb
    have hB1 : CFSG.IsElementaryAbelian 2 ↥(B₀ ⊔ zpowers u) := by
      refine isElementaryAbelian_sup hBel ?_ ?_
      · have hu2' : u ^ 2 = 1 := by rw [pow_two]; exact hu2
        exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hu2'
      · intro b hb z hz
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hz
        exact (Commute.zpow_right (huc b hb) m).eq
    have hmem : B₀ ⊔ zpowers u ∈ s :=
      ⟨hWB.trans le_sup_left, sup_le hBX (zpowers_le.2 huX), hB1⟩
    have hcard := hmax _ hmem
    have heq : B₀ = B₀ ⊔ zpowers u :=
      Subgroup.eq_of_le_of_card_ge le_sup_left hcard
    rw [heq]
    exact Subgroup.mem_sup_right (mem_zpowers u)

@[expose] def ConnStep (r n : ℕ) (X A' A'' : Subgroup G) : Prop :=
  IsE r X A'' ∧ (∀ a ∈ A', ∀ b ∈ A'', a * b = b * a) ∧
    (A' = A'' ∨ n ≤ pRank 2 ↥(X ⊓ centralizer ((A' ⊔ A'' : Subgroup G) : Set G)))

@[expose] def RConnN (r n : ℕ) (X A B : Subgroup G) : Prop :=
  Relation.ReflTransGen (ConnStep r n X) A B

theorem theta_eq_of_le [Finite G] (ℓ : Th2Level) (h218 : B_IG_21_8) (h2110 : B_IG_21_10)
    {A B : Subgroup G} (hB : IsE ℓ.minRank ⊤ B) (hbal : ℓ.IsBal B) (hA : IsE ℓ.r B A) :
    ℓ.theta A = ℓ.theta B := by
  cases ℓ with
  | one => exact h218 G 1 le_rfl B A hB hbal hA
  | three => exact h218 G 3 (by norm_num) B A hB hbal hA
  | fiveHalves => exact h2110 G 2 (by norm_num) B A hB hbal.1 hbal.2 hA

theorem theta_eq_of_connStep [Finite G] (ℓ : Th2Level) (h218 : B_IG_21_8) (h2110 : B_IG_21_10)
    {X A' A'' : Subgroup G}
    (hS : ∀ B' : Subgroup G, IsSn ℓ.n X B' → IsE ℓ.minRank ⊤ B' ∧ ℓ.IsBal B')
    (hA' : IsE ℓ.r X A') (hstep : ConnStep ℓ.r ℓ.n X A' A'') : ℓ.theta A' = ℓ.theta A'' := by
  rcases hstep with ⟨hA'', hcomm, heq | hrk⟩
  · rw [heq]
  · have hV := isElementaryAbelian_sup hA'.2.1 hA''.2.1 hcomm
    obtain ⟨E, hEle, hEel, hErk⟩ := exists_elemAbelian_pRank (X ⊓ centralizer ((A' ⊔ A'' : Subgroup G) : Set G))
    have hEC : E ≤ centralizer ((A' ⊔ A'' : Subgroup G) : Set G) := hEle.trans inf_le_right
    have hEV : ∀ v ∈ A' ⊔ A'', ∀ e ∈ E, v * e = e * v := fun v hv e he =>
      (Subgroup.mem_centralizer_iff.1 (hEC he) v hv)
    have hW := isElementaryAbelian_sup hV hEel hEV
    have hWX : (A' ⊔ A'') ⊔ E ≤ X := sup_le (sup_le hA'.1 hA''.1) (hEle.trans inf_le_left)
    obtain ⟨B₀, hWB₀, hB₀S⟩ := exists_maximal_elemAbelian hWX hW
    have hB₀n : ℓ.n ≤ pRank 2 ↥B₀ :=
      hrk.trans (hErk.ge.trans (C3.Layer1.Back.pRank_mono' (le_sup_right.trans hWB₀)))
    obtain ⟨hB₀E, hB₀bal⟩ := hS B₀ ⟨hB₀S, hB₀n⟩
    have hA'B₀ : IsE ℓ.r B₀ A' :=
      ⟨le_sup_left.trans (le_sup_left.trans hWB₀), hA'.2.1, hA'.2.2⟩
    have hA''B₀ : IsE ℓ.r B₀ A'' :=
      ⟨le_sup_right.trans (le_sup_left.trans hWB₀), hA''.2.1, hA''.2.2⟩
    rw [theta_eq_of_le ℓ h218 h2110 hB₀E hB₀bal hA'B₀,
      theta_eq_of_le ℓ h218 h2110 hB₀E hB₀bal hA''B₀]

theorem theta_eq_of_conn [Finite G] (ℓ : Th2Level) (h218 : B_IG_21_8) (h2110 : B_IG_21_10)
    {X A B : Subgroup G}
    (hS : ∀ B' : Subgroup G, IsSn ℓ.n X B' → IsE ℓ.minRank ⊤ B' ∧ ℓ.IsBal B')
    (hA : IsE ℓ.r X A) (hconn : RConnN ℓ.r ℓ.n X A B) : ℓ.theta A = ℓ.theta B := by
  have key : ∀ C, RConnN ℓ.r ℓ.n X A C → IsE ℓ.r X C ∧ ℓ.theta A = ℓ.theta C := by
    intro C hC
    induction hC with
    | refl => exact ⟨hA, rfl⟩
    | tail _ hstep ih =>
      rename_i b c
      exact ⟨hstep.1, ih.2.trans (theta_eq_of_connStep ℓ h218 h2110 hS ih.1 hstep)⟩
  exact (key B hconn).2

end CFSG.GH74.GLS.Th2
