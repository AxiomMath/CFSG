module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2C3

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

omit [Finite G] in
theorem commute_sup_of_comm {A B : Subgroup G} (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hN : B ≤ Subgroup.normalizer (A : Set G) := le_normalizer_of_commute hAB
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).1 hx
  obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_iff_of_le_normalizer hN).1 hy
  have e1 : a * a' = a' * a := hA a ha a' ha'
  have e2 : b * b' = b' * b := hB b hb b' hb'
  have e3 : a * b' = b' * a := hAB a ha b' hb'
  have e4 : a' * b = b * a' := hAB a' ha' b hb
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [e4]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [e1, e2]
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [e3]
    _ = a' * b' * (a * b) := by group

omit [Finite G] in
theorem conjR_inj_right {X Y : Subgroup G} {b : G} (h : conjR X b = conjR Y b) : X = Y := by
  have := congrArg (fun Z => conjR Z b⁻¹) h
  simpa only [conjR_conjR_inv] using this

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem L₀_le_normalizer_L : conjJoin S L ≤ Subgroup.normalizer (L : Set G) := by
  rw [B.hjoin]
  exact sup_le Subgroup.le_normalizer B.L₂_le_normalizer_L

theorem L_le_L₀ : L ≤ conjJoin S L := B.hjoin ▸ le_sup_left

theorem L₂_le_L₀ : conjR L t ≤ conjJoin S L := B.hjoin ▸ le_sup_right

theorem conjR_cases_of_mem_normalizer {b : G}
    (hb : b ∈ Subgroup.normalizer (conjJoin S L : Set G)) :
    conjR L b = L ∨ conjR L b = conjR L t := by
  refine AppE.conjR_cases_generic B.comm_elem ?_ ?_ (card_conjR L b) (card_conjR L t)
    (fun Y hYL hn => AppE.normal_le_or_eq_lin2 B.hL B.hn B.hlin hYL hn)
    (fun Y hYL hn => AppE.normal_le_or_eq_lin2 B.hL₂ B.hn B.hlin₂ hYL hn)
    (fun a ha h => AppE.mem_blockQ_of_comm_lin2 B.hn B.hlin ha h)
    (fun a ha h => AppE.mem_blockQ_of_comm_lin2 B.hn B.hlin₂ ha h)
    (AppE.three_dvd_card_lin2 B.hlin)
  · rw [← B.hjoin]
    have := conjR_mono B.L_le_L₀ b
    rwa [conjR_eq_of_mem_normalizer hb] at this
  · rw [← B.hjoin]
    have := conjR_mono B.L₀_le_normalizer_L b
    rwa [conjR_eq_of_mem_normalizer hb, ← conjR_normalizer] at this

theorem normalizer_of_odd {b : G} (hb : b ∈ Subgroup.normalizer (conjJoin S L : Set G))
    (hodd : Odd (orderOf b)) :
    b ∈ Subgroup.normalizer (L : Set G) ∧
      b ∈ Subgroup.normalizer ((conjR L t : Subgroup G) : Set G) := by
  have htN : t ∈ Subgroup.normalizer (conjJoin S L : Set G) := S_le_normalizer_conjJoin' S L B.ht
  have htbN : t * b ∈ Subgroup.normalizer (conjJoin S L : Set G) := Subgroup.mul_mem _ htN hb
  have hne := B.hne
  have hL₂ : conjR (conjR L t) b = conjR L (t * b) := conjR_conjR L t b
  have hcases := B.conjR_cases_of_mem_normalizer hb
  have hcases₂ := B.conjR_cases_of_mem_normalizer htbN
  have hLb : conjR L b = L := by
    rcases hcases with h | h
    · exact h
    · exfalso
      rcases hcases₂ with h' | h'
      ·
        have h2 : conjR L (b * b) = L := by rw [← conjR_conjR, h, hL₂, h']
        have hb2 : b * b ∈ Subgroup.normalizer (L : Set G) := conjR_eq_self_iff.1 h2
        obtain ⟨m, hm⟩ := hodd
        have hb1 : b ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one b
        have e : b = (b * b) ^ (m + 1) := by
          calc b = b ^ (2 * m + 1) * b := by rw [hb1, one_mul]
            _ = (b * b) ^ (m + 1) := by
              rw [← pow_two, ← pow_mul, ← pow_succ]
              exact congrArg (b ^ ·) (by omega)
        have hbN : b ∈ Subgroup.normalizer (L : Set G) := by
          rw [e]; exact Subgroup.pow_mem _ hb2 _
        exact hne (h.symm.trans (conjR_eq_of_mem_normalizer hbN))
      ·
        have : conjR (conjR L t) b = conjR L b := by rw [hL₂, h', h]
        exact hne (conjR_inj_right this)
  refine ⟨conjR_eq_self_iff.1 hLb, conjR_eq_self_iff.1 ?_⟩
  rcases hcases₂ with h' | h'
  · exfalso
    have : conjR (conjR L t) b = conjR L b := by rw [hL₂, h', hLb]
    exact hne (conjR_inj_right this)
  · rw [hL₂, h']

theorem hall_le_normalizer_L {B' : Subgroup G} (hH : S2Hall S L D x₀ B') :
    B' ≤ Subgroup.normalizer (L : Set G) ∧
      B' ≤ Subgroup.normalizer ((conjR L t : Subgroup G) : Set G) := by
  have hodd : ∀ b ∈ B', Odd (orderOf b) := by
    intro b hb
    have h1 : orderOf b ∣ Nat.card B' := by
      have := orderOf_dvd_natCard (⟨b, hb⟩ : B')
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hH.odd h1
  exact ⟨fun b hb => (B.normalizer_of_odd (hH.le_L₀ hb) (hodd b hb)).1,
    fun b hb => (B.normalizer_of_odd (hH.le_L₀ hb) (hodd b hb)).2⟩

theorem D_inf_L_eq {D₁ D₂ : Subgroup G} (h₁ : D₁ ≤ L) (h₂ : D₂ ≤ conjR L t) (hD : D = D₁ ⊔ D₂) :
    D ⊓ L = D₁ := by
  apply le_antisymm
  · rintro d ⟨hd, hdL⟩
    rw [hD] at hd
    have hN : D₂ ≤ Subgroup.normalizer (D₁ : Set G) :=
      le_normalizer_of_commute fun a ha b hb => B.comm_elem a (h₁ ha) b (h₂ hb)
    obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).1 hd
    have hd₂L : d₂ ∈ L := by
      have := L.mul_mem (L.inv_mem (h₁ hd₁)) hdL
      simpa using this
    have : d₂ ∈ L ⊓ conjR L t := ⟨hd₂L, h₂ hd₂⟩
    rw [B.L_inf_L₂, Subgroup.mem_bot] at this
    rw [this, mul_one]
    exact hd₁
  · exact le_inf (hD ▸ le_sup_left) h₁

theorem D_inf_L₂_eq {D₁ D₂ : Subgroup G} (h₁ : D₁ ≤ L) (h₂ : D₂ ≤ conjR L t) (hD : D = D₁ ⊔ D₂) :
    D ⊓ conjR L t = D₂ := by
  apply le_antisymm
  · rintro d ⟨hd, hdL⟩
    rw [hD] at hd
    have hN : D₁ ≤ Subgroup.normalizer (D₂ : Set G) :=
      le_normalizer_of_commute fun a ha b hb => (B.comm_elem b (h₁ hb) a (h₂ ha)).symm
    obtain ⟨d₂, hd₂, d₁, hd₁, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).1 (sup_comm D₁ D₂ ▸ hd)
    have hd₁L : d₁ ∈ conjR L t := by
      have := (conjR L t).mul_mem ((conjR L t).inv_mem (h₂ hd₂)) hdL
      simpa using this
    have : d₁ ∈ L ⊓ conjR L t := ⟨h₁ hd₁, hd₁L⟩
    rw [B.L_inf_L₂, Subgroup.mem_bot] at this
    rw [this, mul_one]
    exact hd₂
  · exact le_inf (hD ▸ le_sup_right) h₂

theorem Z_le_W : blockZ L ≤ W := by
  intro u hu
  have hq2 := B.su.loc.q2
  obtain ⟨y, hyB, hyQ⟩ : ∃ y ∈ baum S, y ∉ baum S ⊓ Subgroup.centralizer (blockU L : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : baum S ≤ baum S ⊓ Subgroup.centralizer (blockU L : Set G) := fun y hy => hcon y hy
    have h1 : (baum S ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex (baum S) = 1 :=
      Subgroup.relIndex_eq_one.2 hle
    rw [B.su.loc.rk.idx_Q] at h1
    omega
  have hcentr : ∀ y ∈ thompsonJ S, u * y = y * u := by
    have hR : thompsonJ S ≤ Subgroup.centralizer ({u} : Set G) := by
      rw [B.R_eq_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 hu.2 y hy.2
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (B.comm_elem u (blockU_le L hu.1) y hy.2).symm
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 hy.2 u (B.L_le_L₀ (blockU_le L hu.1))).symm
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hR hy)).symm
  exact (B.su.loc.rk.cent_y y hyB hyQ u hu.1).2 (hcentr y (by rw [B.baum_eq] at hyB; exact hyB))

end S2Base

end CFSG.QuasithinUnique.Lin2
