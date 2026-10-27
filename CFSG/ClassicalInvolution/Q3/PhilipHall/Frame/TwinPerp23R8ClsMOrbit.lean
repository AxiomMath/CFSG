module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsMModel

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsM

open CFSG.ClassicalInvolution.Q3.AE Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model

structure Ident {Q : Type*} [Group Q] (ψ : Q →* AEQ 5) (Φ : Set (Subgroup Q)) : Prop where
  inj : Function.Injective ψ
  label : ∀ L ∈ Φ, ∃ (q : Fin 5) (b : Bool), L.map ψ = memBar (miss q) (card_miss q) b
  surj : ∀ (q : Fin 5) (b : Bool), ∃ L ∈ Φ, L.map ψ = memBar (miss q) (card_miss q) b

section Comb

theorem comb {f g : Fin 5 → Fin 5} {a b p : Fin 5} (hab : a ≠ b) (hpa : p ≠ a) (hpb : p ≠ b)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfab : (f a = a ∧ f b = b) ∨ (f a = b ∧ f b = a))
    (hgab : (g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a)) {k : ℕ} (hk : Odd k) (hgk : g^[k] p = p)
    (hgp : g p ≠ p) : f p = p ∨ f p = g p ∨ f p = g (g p) := by
  classical
  have hT : ∀ {h : Fin 5 → Fin 5}, Function.Injective h →
      ((h a = a ∧ h b = b) ∨ (h a = b ∧ h b = a)) → ∀ x, x ≠ a → x ≠ b → h x ≠ a ∧ h x ≠ b := by
    intro h hh hab' x hxa hxb
    constructor
    · intro hx
      rcases hab' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hxa (hh (hx.trans h1.symm))
      · exact hxb (hh (hx.trans h2.symm))
    · intro hx
      rcases hab' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hxb (hh (hx.trans h2.symm))
      · exact hxa (hh (hx.trans h1.symm))
  have hgg : g (g p) ≠ g p := fun h => hgp (hg h)
  have hgg' : g (g p) ≠ p := by
    intro h2
    have hit : ∀ j : ℕ, g^[2 * j] p = p := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [show 2 * (j + 1) = 2 * j + 2 by ring, Function.iterate_add_apply]
        simpa using (congrArg (g^[2 * j]) h2).trans ih
    obtain ⟨j, hj⟩ := hk
    apply hgp
    have := hgk
    rw [hj, add_comm, Function.iterate_add_apply, hit j] at this
    simpa using this
  set S : Finset (Fin 5) := {p, g p, g (g p)} with hS
  set T : Finset (Fin 5) := Finset.univ \ {a, b} with hTdef
  have hTc : T.card = 3 := by
    rw [hTdef, Finset.card_univ_diff, Finset.card_pair hab]
    simp
  have hmemT : ∀ x, x ∈ T ↔ x ≠ a ∧ x ≠ b := by
    intro x
    simp [hTdef]
  have hSc : S.card = 3 := by
    rw [hS, Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hgg)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hgp, Ne.symm hgg'⟩
  have hgT : ∀ x, x ≠ a → x ≠ b → g x ≠ a ∧ g x ≠ b := hT hg hgab
  have hSsub : S ⊆ T := by
    intro x hx
    rw [hmemT]
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨hpa, hpb⟩
    · exact hgT _ hpa hpb
    · exact hgT _ (hgT _ hpa hpb).1 (hgT _ hpa hpb).2
  have hST : S = T := Finset.eq_of_subset_of_card_le hSsub (by rw [hSc, hTc])
  have hfp : f p ∈ T := by
    rw [hmemT]
    exact hT hf hfab p hpa hpb
  rw [← hST] at hfp
  simpa [hS] using hfp

end Comb

namespace Ident

variable {Q : Type*} [Group Q] {ψ : Q →* AEQ 5} {Φ : Set (Subgroup Q)} (H : Ident ψ Φ)

include H

theorem exists_z (c : Fin 5) : ∃ z : Q, ψ z = zBar (miss c) (card_miss c) := by
  obtain ⟨L, -, hL⟩ := H.surj c true
  have h : zBar (miss c) (card_miss c) ∈ L.map ψ := by
    rw [hL]
    exact zBar_mem_memBar _ _ _
  obtain ⟨z, -, hz⟩ := h
  exact ⟨z, hz⟩

theorem mem_of_psi_eq {L : Subgroup Q} {c : Fin 5} {b : Bool}
    (hL : L.map ψ = memBar (miss c) (card_miss c) b) {z : Q}
    (hz : ψ z = zBar (miss c) (card_miss c)) : z ∈ L := by
  have h : ψ z ∈ L.map ψ := by
    rw [hL, hz]
    exact zBar_mem_memBar _ _ _
  obtain ⟨z', hz', hzz⟩ := h
  rwa [← H.inj hzz]

theorem exists_image {z : Q} {c : Fin 5} (hz : ψ z = zBar (miss c) (card_miss c)) (τ : Q ≃* Q)
    (hτ : ∀ L ∈ Φ, L.map τ.toMonoidHom ∈ Φ) :
    ∃ c' : Fin 5, ψ (τ z) = zBar (miss c') (card_miss c') := by
  obtain ⟨L, hLΦ, hL⟩ := H.surj c true
  have hzL : z ∈ L := H.mem_of_psi_eq hL hz
  obtain ⟨q, b, hq⟩ := H.label _ (hτ L hLΦ)
  have hmem : ψ (τ z) ∈ (L.map τ.toMonoidHom).map ψ :=
    ⟨τ z, ⟨z, hzL, rfl⟩, rfl⟩
  rw [hq] at hmem
  have hzz : z * z = 1 := by
    apply H.inj
    rw [map_mul, hz, zBar_mul_self, map_one]
  have hsq : ψ (τ z) * ψ (τ z) = 1 := by
    rw [← map_mul, ← map_mul, hzz, map_one, map_one]
  rcases eq_of_mem_memBar_mul_self (by norm_num) hmem hsq with h1 | h1
  · exfalso
    have h2 : τ z = 1 := H.inj (by rw [h1, map_one])
    have h3 : z = 1 := τ.injective (by rw [h2, map_one])
    rw [h3, map_one] at hz
    exact zBar_ne_one (by norm_num) (miss c) (card_miss c) hz.symm
  · exact ⟨q, h1⟩

theorem exists_perm (τ : Q ≃* Q) (hτ : ∀ L ∈ Φ, L.map τ.toMonoidHom ∈ Φ) :
    ∃ f : Fin 5 → Fin 5, Function.Injective f ∧ ∀ (c : Fin 5) (z : Q),
      ψ z = zBar (miss c) (card_miss c) → ψ (τ z) = zBar (miss (f c)) (card_miss (f c)) := by
  have h : ∀ c : Fin 5, ∃ c' : Fin 5, ∀ z : Q, ψ z = zBar (miss c) (card_miss c) →
      ψ (τ z) = zBar (miss c') (card_miss c') := by
    intro c
    obtain ⟨z₀, hz₀⟩ := H.exists_z c
    obtain ⟨c', hc'⟩ := H.exists_image hz₀ τ hτ
    refine ⟨c', fun z hz => ?_⟩
    have : z = z₀ := H.inj (hz.trans hz₀.symm)
    rw [this]
    exact hc'
  choose f hf using h
  refine ⟨f, ?_, hf⟩
  intro c d hcd
  obtain ⟨zc, hzc⟩ := H.exists_z c
  obtain ⟨zd, hzd⟩ := H.exists_z d
  have h1 : ψ (τ zc) = ψ (τ zd) := by
    rw [hf c zc hzc, hf d zd hzd, hcd]
  have h2 : zc = zd := τ.injective (H.inj h1)
  rw [h2] at hzc
  exact miss_inj (eq_of_zBar_eq (by norm_num) (hzc.symm.trans hzd))

end Ident

theorem iterate_psi {Q : Type*} [Group Q] {ψ : Q →* AEQ 5} (σ : Q ≃* Q) {g : Fin 5 → Fin 5}
    (hg : ∀ (c : Fin 5) (z : Q), ψ z = zBar (miss c) (card_miss c) →
      ψ (σ z) = zBar (miss (g c)) (card_miss (g c))) (j : ℕ) :
    ∀ (c : Fin 5) (z : Q), ψ z = zBar (miss c) (card_miss c) →
      ψ ((σ : Q → Q)^[j] z) = zBar (miss (g^[j] c)) (card_miss (g^[j] c)) := by
  induction j with
  | zero =>
    intro c z hz
    simpa using hz
  | succ j ih =>
    intro c z hz
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (g c) (σ z) (hg c z hz)

section Three

variable {Q : Type*} [Group Q] {ψ : Q →* AEQ 5} {Φ : Set (Subgroup Q)} (H : Ident ψ Φ)

include H

theorem three_orbit {x v : Q} {p : Fin 5} {ι : Fin 4 ↪ Fin 5} (hι : ∀ y, y ∈ Set.range ι ↔ y ≠ p)
    (hx : ψ x = zBar (miss p) (card_miss p)) (hv : ψ v = mkQ 5 (embed ι w0))
    (τ σ : Q ≃* Q) (hτ : ∀ L ∈ Φ, L.map τ.toMonoidHom ∈ Φ) (hσ : ∀ L ∈ Φ, L.map σ.toMonoidHom ∈ Φ)
    (hτv : τ v = v) (hσv : σ v = v) {k : ℕ} (hk : Odd k) (hσk : ∀ z, (σ : Q → Q)^[k] z = z)
    (hσx : σ x ≠ x) : ∃ j : ℕ, j < 3 ∧ τ x = (σ : Q → Q)^[j] x := by
  obtain ⟨f, hfi, hf⟩ := H.exists_perm τ hτ
  obtain ⟨g, hgi, hg⟩ := H.exists_perm σ hσ
  have hab : ι 0 ≠ ι 1 := ι.injective.ne (by decide)
  have hpa : p ≠ ι 0 := fun h => ((hι (ι 0)).mp ⟨0, rfl⟩) h.symm
  have hpb : p ≠ ι 1 := fun h => ((hι (ι 1)).mp ⟨1, rfl⟩) h.symm
  have key : ∀ (ρ : Q ≃* Q) (h : Fin 5 → Fin 5), Function.Injective h →
      (∀ (c : Fin 5) (z : Q), ψ z = zBar (miss c) (card_miss c) →
        ψ (ρ z) = zBar (miss (h c)) (card_miss (h c))) → ρ v = v →
      (h (ι 0) = ι 0 ∧ h (ι 1) = ι 1) ∨ (h (ι 0) = ι 1 ∧ h (ι 1) = ι 0) := by
    intro ρ h hhi hh hρv
    obtain ⟨za, hza⟩ := H.exists_z (ι 0)
    obtain ⟨zb, hzb⟩ := H.exists_z (ι 1)
    have hvz : v = za * zb := by
      apply H.inj
      rw [map_mul, hza, hzb, hv, mkQ_embed_w0]
    have h1 : zBar (miss (h (ι 0))) (card_miss _) * zBar (miss (h (ι 1))) (card_miss _) =
        zBar (miss (ι 0)) (card_miss _) * zBar (miss (ι 1)) (card_miss _) := by
      calc zBar (miss (h (ι 0))) (card_miss _) * zBar (miss (h (ι 1))) (card_miss _)
          = ψ (ρ za) * ψ (ρ zb) := by rw [hh _ za hza, hh _ zb hzb]
        _ = ψ (ρ (za * zb)) := by rw [map_mul, map_mul]
        _ = ψ (ρ v) := by rw [← hvz]
        _ = ψ v := by rw [hρv]
        _ = zBar (miss (ι 0)) (card_miss _) * zBar (miss (ι 1)) (card_miss _) := by
          rw [hvz, map_mul, hza, hzb]
    exact eq_pair_of_mul_eq (hhi.ne hab) hab h1
  have hfab := key τ f hfi hf hτv
  have hgab := key σ g hgi hg hσv
  have hgk : g^[k] p = p := by
    have h1 := iterate_psi σ hg k p x hx
    rw [hσk x, hx] at h1
    exact (miss_inj (eq_of_zBar_eq (by norm_num) h1)).symm
  have hgp : g p ≠ p := by
    intro h
    apply hσx
    apply H.inj
    rw [hg p x hx, h, hx]
  have hmain := comb hab hpa hpb hfi hgi hfab hgab hk hgk hgp
  have hfx : ψ (τ x) = zBar (miss (f p)) (card_miss _) := hf p x hx
  rcases hmain with h | h | h
  · refine ⟨0, by norm_num, H.inj ?_⟩
    rw [hfx, h]
    exact hx.symm
  · refine ⟨1, by norm_num, H.inj ?_⟩
    have := iterate_psi σ hg 1 p x hx
    rw [hfx, h]
    exact this.symm
  · refine ⟨2, by norm_num, H.inj ?_⟩
    have := iterate_psi σ hg 2 p x hx
    rw [hfx, h]
    exact this.symm

end Three

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsM
