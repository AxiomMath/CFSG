module

public import CFSG.LieType.ChevTwo.OppCl.SmallGlue
public import CFSG.GH74.KGroups.U33
public import Certificates.Certificate214003

public section

namespace CFSG.LieType.ChevTwo.OppCl.U33Fin

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33

theorem checkCenter_eq : checkCenter () = true :=
  Certificates.certificate214003.1

theorem checkExp_eq : checkExp () = true :=
  Certificates.certificate214003.2.1

theorem checkF1_eq : checkF1 () = true :=
  Certificates.certificate214003.2.2.1

theorem checkF3_eq : checkF3 () = true :=
  Certificates.certificate214003.2.2.2.1

theorem checkX5_eq : checkX5 () = true :=
  Certificates.certificate214003.2.2.2.2

theorem mem_invsOf {L : List (Equiv.Perm (Fin 28))} {s : Equiv.Perm (Fin 28)} :
    s ∈ invsOf L ↔ s ∈ L ∧ s * s = 1 ∧ s ≠ 1 := by
  simp [invsOf, List.mem_filter]

theorem mem_o3Of {L : List (Equiv.Perm (Fin 28))} {x : Equiv.Perm (Fin 28)} :
    x ∈ o3Of L ↔ x ∈ L ∧ x ^ 3 = 1 ∧ x ≠ 1 := by
  simp [o3Of, List.mem_filter]

theorem center_prop :
    ∀ g ∈ elems (), g * pa = pa * g → g * pb = pb * g → g = 1 := by
  intro g hg h1 h2
  have h := checkCenter_eq
  simp only [checkCenter, List.all_eq_true] at h
  have hx := h g hg
  simp [h1, h2] at hx
  exact hx

theorem exp_prop : ∀ x ∈ elems (), x ^ 27 = 1 → x ^ 3 = 1 := by
  intro x hx h27
  have h := checkExp_eq
  simp only [checkExp, List.all_eq_true] at h
  have hx' := h x hx
  simp [h27] at hx'
  exact hx'

theorem F1_prop :
    ∀ g ∈ elems (), g ^ 7 = 1 → g ≠ 1 → ∀ s ∈ invsOf (elems ()), g * s ≠ s * g := by
  intro g hg h7 h1 s hs hgs
  have h := checkF1_eq
  simp only [checkF1, checkF1', List.all_eq_true] at h
  have hx := h g hg
  have hx' : (!(g ^ 7 == 1 && g != 1)) = false := by simp [h7, h1]
  rw [hx', Bool.false_or] at hx
  have hy := List.all_eq_true.1 hx s hs
  simp [hgs] at hy

theorem F3_prop :
    ∀ g ∈ o3Of (elems ()), ∀ h ∈ o3Of (elems ()), g * h = h * g → h ≠ g →
    h ≠ g * g → ∃ x ∈ [g, h, g * h, g * h * h], ∀ s ∈ invsOf (elems ()), x * s ≠ s * x := by
  intro g hg h hh hgh hhg hhgg
  have hc := checkF3_eq
  simp only [checkF3, checkF3', List.all_eq_true] at hc
  have hx := hc g hg h hh
  rw [show (!(g * h == h * g && h != g && h != g * g)) = false by
    simp [hgh, hhg, hhgg], Bool.false_or] at hx
  obtain ⟨x, hxmem, hxI⟩ := List.any_eq_true.1 hx
  refine ⟨x, hxmem, fun s hs hxs => ?_⟩
  have hy := List.all_eq_true.1 hxI s hs
  simp [hxs] at hy

theorem X5_prop :
    ∀ g ∈ o3Of (elems ()), ∀ s ∈ invsOf (elems ()), g * s = s * g →
    ∃ c ∈ (elems ()).filter (fun c => g * c == c * g),
      (s * (c * s * c⁻¹)) ^ 3 = 1 ∧ s * (c * s * c⁻¹) ≠ 1 := by
  intro g hg s hs hgs
  have hc := checkX5_eq
  simp only [checkX5, checkX5'] at hc
  have hany : (invsOf (elems ())).any (fun s => g * s == s * g) = true :=
    List.any_eq_true.2 ⟨s, hs, by simp [hgs]⟩
  have hg' := List.all_eq_true.1 hc g hg
  rw [if_pos hany] at hg'
  have hs' := List.all_eq_true.1 hg' s hs
  simp only [hgs, beq_self_eq_true, Bool.not_true, Bool.false_or] at hs'
  obtain ⟨c, hcC, hcv⟩ := List.any_eq_true.1 hs'
  refine ⟨c, hcC, ?_⟩
  simpa using hcv

theorem pa_mem : pa ∈ elems () :=
  (mem_elemsT QP QP_ok pa).2 (by
    rw [QP_closure]; exact Subgroup.subset_closure (Set.mem_insert _ _))

theorem pb_mem : pb ∈ elems () :=
  (mem_elemsT QP QP_ok pb).2 (by
    rw [QP_closure]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem oppositeFixed_of_iso
    {K : Type} [Group K] (e : K ≃* QP.originalSubgroup) : OppositeFixed K := by
  set ψ : K →* Equiv.Perm (Fin 28) := QP.originalSubgroup.subtype.comp e.toMonoidHom with hψdef
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp e.injective
  have hψmem : ∀ x, ψ x ∈ elems () := fun x => (mem_elemsT QP QP_ok _).2 (e x).2
  have hsurj : ∀ y ∈ elems (), ∃ x : K, ψ x = y := fun y hy =>
    ⟨e.symm ⟨y, (mem_elemsT QP QP_ok y).1 hy⟩, by simp [hψdef]⟩
  have hψone : ∀ x, ψ x = 1 → x = 1 := fun x h => hψinj (by rw [h, map_one])
  have hK : Nat.card K = 6048 := by
    rw [Nat.card_congr e.toEquiv, card_group QP QP_ok]
    exact QP_valid.2
  haveI : Finite K := Finite.of_equiv QP.originalSubgroup e.symm.toEquiv
  haveI : Finite (MulAut K) := finite_mulAut e
  refine oppositeFixed_of_u33_facts (card_mulAut e) hK ?_ ?_ ?_ ?_ ?_
  ·
    intro z hz
    apply hψone
    apply center_prop (ψ z) (hψmem z)
    · obtain ⟨x, hx⟩ := hsurj pa pa_mem
      rw [← hx, ← map_mul, ← map_mul, hz x]
    · obtain ⟨x, hx⟩ := hsurj pb pb_mem
      rw [← hx, ← map_mul, ← map_mul, hz x]
  ·
    intro x hx27
    apply hψinj
    rw [map_pow, map_one]
    exact exp_prop (ψ x) (hψmem x) (by rw [← map_pow, hx27, map_one])
  ·
    intro g s hg7 hg1 hs2 hs1 hgs
    have hsI : ψ s ∈ invsOf (elems ()) :=
      mem_invsOf.2 ⟨hψmem s, by rw [← map_mul, hs2, map_one], fun h => hs1 (hψone s h)⟩
    exact F1_prop (ψ g) (hψmem g) (by rw [← map_pow, hg7, map_one])
      (fun h => hg1 (hψone g h)) (ψ s) hsI (by rw [← map_mul, ← map_mul, hgs])
  ·
    intro g h hg3 hg1 hh3 hh1 hgh hhg hhgg
    have hgo : ψ g ∈ o3Of (elems ()) :=
      mem_o3Of.2 ⟨hψmem g, by rw [← map_pow, hg3, map_one], fun h' => hg1 (hψone g h')⟩
    have hho : ψ h ∈ o3Of (elems ()) :=
      mem_o3Of.2 ⟨hψmem h, by rw [← map_pow, hh3, map_one], fun h' => hh1 (hψone h h')⟩
    have hcomm : ψ g * ψ h = ψ h * ψ g := by rw [← map_mul, ← map_mul, hgh]
    have hne1 : ψ h ≠ ψ g := fun h' => hhg (hψinj h')
    have hne2 : ψ h ≠ ψ g * ψ g := fun h' => hhgg (hψinj (by rw [map_mul]; exact h'))
    obtain ⟨x', hx'mem, hx's⟩ := F3_prop (ψ g) hgo (ψ h) hho hcomm hne1 hne2
    obtain ⟨x, hxcases, hxψ⟩ : ∃ x : K, (x = g ∨ x = h ∨ x = g * h ∨ x = g * h * h) ∧
        ψ x = x' := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'mem
      rcases hx'mem with rfl | rfl | rfl | rfl
      · exact ⟨g, Or.inl rfl, rfl⟩
      · exact ⟨h, Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨g * h, Or.inr (Or.inr (Or.inl rfl)), by rw [map_mul]⟩
      · exact ⟨g * h * h, Or.inr (Or.inr (Or.inr rfl)), by rw [map_mul, map_mul]⟩
    refine ⟨x, hxcases, fun s hs2 hs1 hxs => ?_⟩
    have hsI : ψ s ∈ invsOf (elems ()) :=
      mem_invsOf.2 ⟨hψmem s, by rw [← map_mul, hs2, map_one], fun h' => hs1 (hψone s h')⟩
    apply hx's (ψ s) hsI
    rw [← hxψ, ← map_mul, ← map_mul, hxs]
  ·
    intro g s hg3 hg1 hs2 hs1 hgs
    have hgo : ψ g ∈ o3Of (elems ()) :=
      mem_o3Of.2 ⟨hψmem g, by rw [← map_pow, hg3, map_one], fun h' => hg1 (hψone g h')⟩
    have hsI : ψ s ∈ invsOf (elems ()) :=
      mem_invsOf.2 ⟨hψmem s, by rw [← map_mul, hs2, map_one], fun h' => hs1 (hψone s h')⟩
    obtain ⟨c', hc'mem, hc'3, hc'1⟩ := X5_prop (ψ g) hgo (ψ s) hsI
      (by rw [← map_mul, ← map_mul, hgs])
    simp only [List.mem_filter, beq_iff_eq] at hc'mem
    obtain ⟨hc'L, hc'g⟩ := hc'mem
    obtain ⟨c, hcψ⟩ := hsurj c' hc'L
    have hψconj : ψ (s * (c * s * c⁻¹)) = ψ s * (c' * ψ s * c'⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, hcψ]
    refine ⟨c, ?_, ?_, ?_⟩
    · apply hψinj
      rw [map_mul, map_mul, hcψ]
      exact hc'g
    · apply hψinj
      rw [map_pow, map_one, hψconj]
      exact hc'3
    · intro h
      apply hc'1
      rw [← hψconj, h, map_one]

end CFSG.LieType.ChevTwo.OppCl.U33Fin
