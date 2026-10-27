module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf14Aut
public import CFSG.ClassicalInvolution.Q3.TL3T51A

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem aeAut_eight : AEAut 8 := by
  intro H hH σ hσ hperm
  subst hH
  let β : MulAut ↥(Hn 8) := MulEquiv.ofBijective σ hσ
  obtain ⟨x, hx⟩ := CFSG.ClassicalInvolution.Q3.TC.Thin.model117At_eight β (fun α h b => by
    obtain ⟨β', hβ', c', hm⟩ := hperm α h b
    refine ⟨β', hβ', c', ?_⟩
    have hle : ((memBar α h b).subgroupOf (Hn 8)).map β.toMonoidHom ≤
        (memBar β' hβ' c').subgroupOf (Hn 8) := by
      rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hm y (Subgroup.mem_subgroupOf.mp hy))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have e1 := natCard_subgroupOf_memBar' (by norm_num) β' hβ' c'
    have e2 := natCard_map_subgroupOf' (by norm_num) σ hσ.1 α h b
    exact (e1.trans e2.symm).le)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (piSub 8) x
  exact ⟨w, hx⟩

private theorem n8_klein_regular : ∀ i j : Fin 4,
    ∃ d ∈ ([1, d₁, d₂, d₃] : List (Equiv.Perm (Fin 4))), d i = j ∧ d (d i) = i := by
  decide +kernel

private theorem n8_d₁_ne : ∀ i : Fin 4, d₁ i ≠ i := by decide +kernel

private theorem n8_sq_apply {n : ℕ} (ι : Fin 4 ↪ Fin n) (σ : Equiv.Perm (Fin n))
    (hc : ∀ d ∈ ([1, d₁, d₂, d₃] : List (Equiv.Perm (Fin 4))),
      σ * embedPerm ι d = embedPerm ι d * σ) (i : Fin 4) :
    σ (σ (ι i)) = ι i := by
  have hmem : σ (ι i) ∈ Set.range ι := by
    by_contra hnot
    have h1 := congrArg (fun f : Equiv.Perm (Fin n) => f (ι i)) (hc d₁ (by simp))
    simp only [Equiv.Perm.mul_apply] at h1
    rw [embedPerm_of_not_mem ι d₁ hnot, embedPerm_apply] at h1
    exact n8_d₁_ne i (ι.injective (σ.injective h1))
  obtain ⟨j, hj⟩ := hmem
  obtain ⟨d, hd, hdi, hdd⟩ := n8_klein_regular i j
  have hcd := congrArg (fun f : Equiv.Perm (Fin n) => f (ι i)) (hc d hd)
  simp only [Equiv.Perm.mul_apply, embedPerm_apply] at hcd
  rw [hdi, ← hj, embedPerm_apply] at hcd
  rw [← hj, hcd, ← hdi, hdd]

private theorem n8_perm_eq {n : ℕ} {a b : Wr n} (h : mkQ n a = mkQ n b) : a.perm = b.perm := by
  have := congrArg (CFSG.ClassicalInvolution.Q3.TL4.Mdl117.permQ n) h
  simpa only [CFSG.ClassicalInvolution.Q3.TL4.Mdl117.permQ_mkQ] using this

private theorem n8_comm_klein {n : ℕ} (α : Finset (Fin n)) (hα : α.card = 4) (w : Wr n)
    (hB : ∀ x ∈ memBar α hα true, mkQ n w * x * (mkQ n w)⁻¹ = x) :
    ∀ d ∈ ([1, d₁, d₂, d₃] : List (Equiv.Perm (Fin 4))),
      w.perm * embedPerm (emb α hα) d = embedPerm (emb α hα) d * w.perm := by
  have key : ∀ k : Wr 4, k ∈ kQ →
      w.perm * embedPerm (emb α hα) k.perm = embedPerm (emb α hα) k.perm * w.perm := by
    intro k hk
    have hx : mkQ n (embed (emb α hα) k) ∈ memBar α hα true := ⟨embed (emb α hα) k, ⟨k, hk, rfl⟩, rfl⟩
    have h := hB _ hx
    rw [← map_inv, ← map_mul, ← map_mul] at h
    have hp := n8_perm_eq h
    rw [mul_perm, mul_perm, inv_perm, embed_perm] at hp
    calc w.perm * embedPerm (emb α hα) k.perm
        = (w.perm * embedPerm (emb α hα) k.perm * w.perm⁻¹) * w.perm := by group
      _ = embedPerm (emb α hα) k.perm * w.perm := by rw [hp]
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · rw [embedPerm_one, mul_one, one_mul]
  · exact key ⟨vec4 [0, 2], d₁⟩ (mem_kQ.mpr (by decide +kernel))
  · exact key ⟨vec4 [0, 3], d₂⟩ (mem_kQ.mpr (by decide +kernel))
  · exact key ⟨vec4 [0, 1], d₃⟩ (mem_kQ.mpr (by decide +kernel))

theorem aePerm_eight : AEPerm 8 := by
  classical
  intro α hα w ⟨a, hA⟩ hB
  right
  have hαc : (αᶜ).card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hα]
  have hc1 := n8_comm_klein α hα w (hB α hα true (Or.inr rfl))
  have hc2 := n8_comm_klein αᶜ hαc w (hB αᶜ hαc true (Or.inl disjoint_compl_right))
  have hsq : w.perm * w.perm = 1 := by
    refine Equiv.ext fun x => ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    by_cases hx : x ∈ α
    · obtain ⟨i, rfl⟩ : x ∈ Set.range (emb α hα) := by
        rw [range_emb]; exact Finset.mem_coe.mpr hx
      exact n8_sq_apply (emb α hα) w.perm hc1 i
    · obtain ⟨i, rfl⟩ : x ∈ Set.range (emb αᶜ hαc) := by
        rw [range_emb]; exact Finset.mem_coe.mpr (Finset.mem_compl.mpr hx)
      exact n8_sq_apply (emb αᶜ hαc) w.perm hc2 i
  have hw4 : w ^ 4 = 1 := by
    have h2 : (w ^ 2).perm = 1 := by rw [sq, mul_perm, hsq]
    have hv : w ^ 4 = (w ^ 2) * (w ^ 2) := by rw [← pow_add]
    rw [hv]
    refine Wr.ext (funext fun t => ?_) (by rw [mul_perm, h2, mul_one]; rfl)
    show (w ^ 2).vec t + (w ^ 2).vec ((w ^ 2).perm.symm t) = 0
    rw [h2]
    exact zmod_two_add_self _
  have hpow : ∃ k : ℕ, (w ^ 3 ^ a) ^ k = w := by
    have h4 : 3 ^ a % 4 = 1 ∨ 3 ^ a % 4 = 3 := by
      have : 3 ^ a % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have hodd : 3 ^ a % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
      omega
    rcases h4 with h | h
    · refine ⟨1, ?_⟩
      rw [pow_one, pow_eq_pow_mod _ hw4, h, pow_one]
    · refine ⟨3, ?_⟩
      rw [← pow_mul, pow_eq_pow_mod _ hw4, Nat.mul_mod, h]
      norm_num
  obtain ⟨k, hk⟩ := hpow
  intro x hx
  have hit : ∀ m : ℕ, mkQ 8 ((w ^ 3 ^ a) ^ m) * x * (mkQ 8 ((w ^ 3 ^ a) ^ m))⁻¹ = x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, map_mul, mul_inv_rev]
      calc mkQ 8 ((w ^ 3 ^ a) ^ m) * mkQ 8 (w ^ 3 ^ a) * x *
            ((mkQ 8 (w ^ 3 ^ a))⁻¹ * (mkQ 8 ((w ^ 3 ^ a) ^ m))⁻¹)
          = mkQ 8 ((w ^ 3 ^ a) ^ m) *
              (mkQ 8 (w ^ 3 ^ a) * x * (mkQ 8 (w ^ 3 ^ a))⁻¹) *
              (mkQ 8 ((w ^ 3 ^ a) ^ m))⁻¹ := by group
        _ = x := by rw [hA x hx, ih]
  have := hit k
  rwa [hk] at this

theorem aeThree_eight : AEThree 8 :=
  aeThree_of_aut_perm aeAut_eight aePerm_eight

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8
