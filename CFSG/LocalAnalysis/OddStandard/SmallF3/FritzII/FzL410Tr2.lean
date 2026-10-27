module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410TrH

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup _root_.Certificates

namespace Fz410Mod

variable {G : Type} [Group G] [Finite G] {t tau lam rho s : G} {Z E W Q R T P : Subgroup G}
  {emb : FzL410.A → G} (M : Fz410Mod t tau lam rho s Z E W Q R T P emb)

include M

private theorem mem_CR (y x : FzL410.TM) :
    fz410Mu emb t s lam x ∈ fz410CR R (fz410Mu emb t s lam y) ↔ FzL410.CR y x := by
  unfold fz410CR FzL410.CR
  rw [Subgroup.mem_inf, M.mem_R, Subgroup.mem_centralizer_singleton_iff, M.mu_comm_iff]

private theorem mem_ZCR (y x : FzL410.TM) :
    fz410Mu emb t s lam x ∈ fz410ZCR R (fz410Mu emb t s lam y) ↔ FzL410.ZCR y x := by
  have hle : fz410CR R (fz410Mu emb t s lam y) ≤ T := inf_le_left.trans M.str.RT
  unfold fz410ZCR FzL410.ZCR
  rw [Subgroup.mem_inf, M.mem_CR, Subgroup.mem_centralizer_iff]
  refine and_congr Iff.rfl ⟨fun h c hc => ?_, fun h g hg => ?_⟩
  · have := h _ ((M.mem_CR y c).mpr hc)
    exact ((M.mu_comm_iff c x).mp this).symm
  · obtain ⟨c, rfl⟩ := (M.mem_T g).mp (hle hg)
    have hcC : FzL410.CR y c := (M.mem_CR y c).mp hg
    exact (M.mu_comm_iff c x).mpr (h c hcC).symm

private theorem mem_S (x : FzL410.TM) :
    fz410Mu emb t s lam x ∈ T ⊓ centralizer ({t} : Set G) ↔ FzL410.inS x := by
  have hT : fz410Mu emb t s lam x ∈ T := (M.mem_T _).mpr ⟨x, rfl⟩
  have h1 := M.mu_comm_iff x FzL410.tM
  rw [M.mu_tM] at h1
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h1.mp h.2, fun h => ⟨hT, h1.mpr h⟩⟩

private theorem mem_CS (a b x : FzL410.TM) :
    fz410Mu emb t s lam x ∈ fz410CS T t (fz410Mu emb t s lam a) (fz410Mu emb t s lam b) ↔
      FzL410.CS a b x := by
  have h1 := M.mem_S x
  unfold fz410CS FzL410.CS
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, M.mu_comm_iff x a, M.mu_comm_iff x b,
    ← h1, Subgroup.mem_inf, and_assoc]

private theorem mem_ZCS (a b x : FzL410.TM) :
    fz410Mu emb t s lam x ∈ fz410ZCS T t (fz410Mu emb t s lam a) (fz410Mu emb t s lam b) ↔
      FzL410.ZCS a b x := by
  have hle : fz410CS T t (fz410Mu emb t s lam a) (fz410Mu emb t s lam b) ≤ T :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  unfold fz410ZCS FzL410.ZCS
  rw [Subgroup.mem_inf, M.mem_CS, Subgroup.mem_centralizer_iff]
  refine and_congr Iff.rfl ⟨fun h c hc => ?_, fun h g hg => ?_⟩
  · have := h _ ((M.mem_CS a b c).mpr hc)
    exact ((M.mu_comm_iff c x).mp this).symm
  · obtain ⟨c, rfl⟩ := (M.mem_T g).mp (hle hg)
    have hcC : FzL410.CS a b c := (M.mem_CS a b c).mp hg
    exact (M.mu_comm_iff c x).mpr (h c hcC).symm

private theorem fus_of_model (y : FzL410.TM) (hy : FzL410.FusAt y) (hyR : FzL410.inR y) :
    Fz410Fus R Z (fz410Mu emb t s lam y) := by
  obtain ⟨hcard, hsq, hzc, hcls⟩ := hy
  refine ⟨(M.mem_R y).mpr hyR, ?_, ?_, ?_, ?_⟩
  · rw [M.card_eq_filter (fz410CR R (fz410Mu emb t s lam y)) (inf_le_left.trans M.str.RT)
      (FzL410.CR y) (M.mem_CR y)]
    exact hcard
  · obtain ⟨x, x', hxx⟩ := hsq
    obtain ⟨hxC, hx'C, hx1, hx'1, hxx'⟩ := hxx
    refine ⟨fz410Mu emb t s lam x, (M.mem_CR y x).mpr hxC, fz410Mu emb t s lam x',
      (M.mem_CR y x').mpr hx'C, ?_, ?_, ?_⟩
    · rw [M.mu_sq]
      intro h
      exact hx1 (M.mu_inj (by rw [h, M.mu_one]))
    · rw [M.mu_sq]
      intro h
      exact hx'1 (M.mu_inj (by rw [h, M.mu_one]))
    · rw [M.mu_sq, M.mu_sq]
      intro h
      exact hxx' (M.mu_inj h)
  · rw [M.card_eq_filter (fz410ZCR R (fz410Mu emb t s lam y))
      ((inf_le_left : fz410ZCR R (fz410Mu emb t s lam y) ≤ fz410CR R (fz410Mu emb t s lam y)).trans
        (inf_le_left.trans M.str.RT)) (FzL410.ZCR y) (M.mem_ZCR y)]
    exact hzc
  · intro r hr
    obtain ⟨r', rfl⟩ := (M.mem_T r).mp (M.str.RT hr)
    obtain ⟨a, b, hab⟩ := hcls r' ((M.mem_R r').mp hr)
    have hZA : ∀ a b : ZMod 2, FzL410.ZA ((2 : ZMod 4) * (a.val : ZMod 4),
        (2 : ZMod 4) * (b.val : ZMod 4), 0, 0) := by decide +kernel
    refine ⟨fz410Mu emb t s lam (FzL410.zE a b), ?_, ?_⟩
    · show fz410Mu emb t s lam (FzL410.pe _) ∈ Z
      rw [M.mu_pe]
      exact (M.mem_Z _).mpr (hZA a b)
    · have h1 : fz410Mu emb t s lam r' * fz410Mu emb t s lam y =
          (fz410Mu emb t s lam y * fz410Mu emb t s lam (FzL410.zE a b)) *
            fz410Mu emb t s lam r' := by
        rw [← M.mu_mul, hab, M.mu_mul, M.mu_mul]
      rw [h1]
      group

theorem fus_transfer (h : FzL410.FusAll) :
    Fz410Fus R Z t ∧ ∀ e ∈ E, Fz410Fus R Z (e * (t * s)) := by
  obtain ⟨ht, hts⟩ := h
  constructor
  · have := M.fus_of_model FzL410.tM ht rfl
    rwa [M.mu_tM] at this
  · intro e he
    obtain ⟨a, b, rfl⟩ := M.exists_eE he
    have := M.fus_of_model (FzL410.mulT (FzL410.eE a b) FzL410.tsM) (hts a b) rfl
    rwa [M.mu_mul, M.mu_eE, M.mu_tsM] at this

theorem cardS_transfer (h : FzL410.CardS) : Nat.card ↥(T ⊓ centralizer ({t} : Set G)) = 128 := by
  rw [M.card_eq_filter _ inf_le_left FzL410.inS M.mem_S]
  exact h

theorem slem_transfer (h : FzL410.SLem) :
    ∀ a ∈ T ⊓ centralizer ({t} : Set G), ∀ b ∈ T ⊓ centralizer ({t} : Set G),
      a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a ≠ b → a * b = b * a →
      Nat.card (fz410CS T t a b) = 64 → (∀ x ∈ fz410CS T t a b, x ^ 4 = 1) →
      Nat.card (fz410ZCS T t a b) = 8 → fz410CS T t a b ≤ R := by
  intro a ha b hb ha2 hb2 ha1 hb1 hab hcomm hcard hexp hzc g hg
  obtain ⟨a', rfl⟩ := (M.mem_T a).mp (Subgroup.mem_inf.mp ha).1
  obtain ⟨b', rfl⟩ := (M.mem_T b).mp (Subgroup.mem_inf.mp hb).1
  have hleCS : fz410CS T t (fz410Mu emb t s lam a') (fz410Mu emb t s lam b') ≤ T :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hleZ : fz410ZCS T t (fz410Mu emb t s lam a') (fz410Mu emb t s lam b') ≤ T :=
    inf_le_left.trans hleCS
  have hrow := h a' b' ((M.mem_S a').mp ha) ((M.mem_S b').mp hb)
    (M.mu_inj (by rw [← M.mu_sq, M.mu_one]; exact ha2))
    (M.mu_inj (by rw [← M.mu_sq, M.mu_one]; exact hb2))
    (fun h' => ha1 (by rw [h', M.mu_one])) (fun h' => hb1 (by rw [h', M.mu_one]))
    (fun h' => hab (by rw [h'])) ((M.mu_comm_iff a' b').mp hcomm)
    (by rw [← M.card_eq_filter _ hleCS (FzL410.CS a' b') (M.mem_CS a' b')]; exact hcard)
    (fun x hx => M.mu_inj (by
      have h4 := hexp _ ((M.mem_CS a' b' x).mpr hx)
      have h5 : fz410Mu emb t s lam x ^ 4 =
          (fz410Mu emb t s lam x * fz410Mu emb t s lam x) *
            (fz410Mu emb t s lam x * fz410Mu emb t s lam x) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [M.mu_mul, M.mu_mul, M.mu_one]
      rw [h5] at h4
      exact h4))
    (by rw [← M.card_eq_filter _ hleZ (FzL410.ZCS a' b') (M.mem_ZCS a' b')]; exact hzc)
  obtain ⟨x, rfl⟩ := (M.mem_T g).mp (hleCS hg)
  exact (M.mem_R x).mpr (hrow x ((M.mem_CS a' b' x).mp hg))

end Fz410Mod

end CFSG.OddStandard.SmallF3.FritzII
