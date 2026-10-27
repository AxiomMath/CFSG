module

public import CFSG.Certificates.Kernel.MathieuAut.ColsKSound

public section

namespace CFSG.KS.MathieuAut

open CFSG.Quasithin.H.Mathieu

theorem memK_spec {L : List (Array ℕ)} {P : Array ℕ → Bool}
    (h : (L.all fun a => a.size == 24 && inAutK a && P a) = true) (a : Array ℕ) (ha : a ∈ L) :
    a.size = 24 ∧ inAutOK a = true ∧ P a = true := by
  have h1 := List.all_eq_true.1 h a ha
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact ⟨h1.1.1, (inAutOK_eq_K a).trans h1.1.2, h1.2⟩

theorem fixAll_cols_spec {act : Array ℕ → ℕ → ℕ} {cols : List ℕ → List ℕ}
    (hact : ∀ a : Array ℕ, a.size = 24 → ∀ m, act a m = actM (cols a.toList) m)
    {L : List (Array ℕ)} (hsz : ∀ a ∈ L, a.size = 24) {N : ℕ} {rel : ℕ → ℕ → Bool}
    {ok : ℕ → Bool} (h : fixAll (L.map fun a => cols a.toList) N rel ok = true) (m : ℕ)
    (hm : m < N) (hfix : ∀ a ∈ L, rel (act a m) m = true) : ok m = true := by
  refine fixAll_spec h m hm fun M hM => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hM
  rw [← hact a (hsz a ha)]
  exact hfix a ha

theorem map_act_cols {act : Array ℕ → ℕ → ℕ} {cols : List ℕ → List ℕ}
    (hact : ∀ a : Array ℕ, a.size = 24 → ∀ m, act a m = actM (cols a.toList) m)
    {L : List (Array ℕ)} (hsz : ∀ a ∈ L, a.size = 24) (v : ℕ) :
    (L.map fun a => act a v) = L.map fun a => actM (cols a.toList) v :=
  List.map_congr_left fun a ha => hact a (hsz a ha) v

end CFSG.KS.MathieuAut

end
