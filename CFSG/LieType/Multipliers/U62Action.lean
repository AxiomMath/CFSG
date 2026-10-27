module

public import CFSG.Certificates.CosetTableOrders
public import CFSG.LieType.Multipliers.KernelStructure

public section

namespace CFSG.LieType.Multipliers

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

@[expose] def actionCheck (ws : List (List (Fin m × Bool))) (S : List ℕ) (k cap n : ℕ)
    (fix move : List (List (Fin m × Bool))) : Bool :=
  let P := colParamsShort ws ((subsetOf m S).map fun x => [(x, true)]) k
  let st := enumerateHLT P cap
  let δ : ℕ → ℕ → ℕ := fun c x => st.tab.getD (c * P.L + x) 0
  (!st.overflow && st.complete P.L && st.liveCount == n) &&
    invConsistentNative P.L (colInv ws) st && relsClosedNative P.L st (colCodes ws ws) &&
    fix.all (fun u => allBelow (fun c => !st.live c ||
      (u.map (colCode ws)).foldl δ c == c) st.next) &&
    move.all fun u => (u.map (colCode ws)).foldl δ 1 != 1

theorem subsetCheckShortC_of_actionCheck {ws : List (List (Fin m × Bool))} {S : List ℕ}
    {k cap n : ℕ} {fix move : List (List (Fin m × Bool))}
    (h : actionCheck ws S k cap n fix move = true) : subsetCheckShortC ws S k cap n = true := by
  unfold actionCheck at h
  unfold subsetCheckShortC checkHLT
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩ := h
  exact h1

theorem exists_hom_of_actionCheck {ws : List (List (Fin m × Bool))} {S : List ℕ} {k cap n : ℕ}
    {fix move : List (List (Fin m × Bool))} (h : actionCheck ws S k cap n fix move = true) :
    ∃ (E : Type) (_ : Group E) (ψ : PG m ws →* E),
      (∀ u ∈ fix, ψ (PresentedGroup.mk _ (FreeGroup.mk u)) = 1) ∧
        ∀ u ∈ move, ψ (PresentedGroup.mk _ (FreeGroup.mk u)) ≠ 1 := by
  unfold actionCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hc⟩, -⟩, hi⟩, hrel⟩, hfix⟩, hmove⟩ := h
  set P := colParamsShort ws ((subsetOf m S).map fun x => [(x, true)]) k
  set st := enumerateHLT P cap
  have hL : P.L = (cols ws).length := rfl
  rw [hL] at hc hi hrel hfix hmove
  set Lc := (cols ws).length
  let δ : ℕ → ℕ → ℕ := fun c x => st.tab.getD (c * Lc + colOfCode ws x) 0
  have hlive : ∀ c, st.live c = true → ∀ x < 2 * m, st.live (δ c x) = true :=
    fun c hl x hx => St.complete_step hc hl (colOfCode_lt ws hx)
  have hinv : ∀ c, st.live c = true → ∀ x < 2 * m, δ (δ c x) (invCode x) = c := by
    intro c hl x hx
    have := invConsistent_spec hi hl (colOfCode_lt ws hx)
    simp only [δ, colOfCode_invCode ws hx]
    exact this
  have hrel' : ∀ c, st.live c = true → ∀ r ∈ codes ws, r.foldl δ c = c := by
    intro c hl r hr
    simp only [codes, List.mem_map] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    show (v.map letterCode).foldl (fun c x => st.tab.getD (c * Lc + colOfCode ws x) 0) c = c
    rw [foldl_colOfCode]
    exact relsClosed_spec hrel hl (List.mem_map_of_mem hv)
  obtain ⟨ψ, hψ⟩ := exists_action_step ws (fun c => st.live c = true) δ hlive hinv hrel'
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  have hw : ∀ u : List (Fin m × Bool), ∀ y ∈ u.map letterCode, y < 2 * m := by
    intro u y hy
    simp only [List.mem_map] at hy
    obtain ⟨x, -, rfl⟩ := hy
    unfold letterCode
    have := x.1.isLt
    split <;> omega
  have hact : ∀ (u : List (Fin m × Bool)) (c : {c : ℕ // st.live c = true}),
      ((ψ (PresentedGroup.mk rels (FreeGroup.mk u))).unop c).1 =
        (u.map (colCode ws)).foldl (fun c x => st.tab.getD (c * Lc + x) 0) c.1 := by
    intro u c
    rw [← evalWord_presLetter, act_evalWord_step ψ hψ _ (hw u) c]
    exact foldl_colOfCode ws st Lc u c.1
  refine ⟨_, inferInstance, ψ, fun u hu => ?_, fun u hu => ?_⟩
  · apply MulOpposite.unop_injective
    ext c
    rw [hact u c]
    have := (allBelow_iff _ _).mp (hfix u hu) c.1 (St.live_lt c.2).2
    simp only [c.2, Bool.not_true, Bool.false_or, beq_iff_eq] at this
    exact this
  · intro h1
    have hone := St.live_one hc
    have := hact u ⟨1, hone⟩
    rw [h1] at this
    exact hmove u hu this.symm

section ThreeTwoTwo

variable {G : Type*} [Group G]

private abbrev Z322 : Type :=
  Multiplicative (ZMod 3) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

private theorem prime_two_or_three {p : ℕ} (hp : p.Prime) (h : p ∣ 12) : p = 2 ∨ p = 3 := by
  have h12 : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  rw [h12] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)

private theorem m3_sq : ∀ a : Multiplicative (ZMod 3), a * a = 1 → a = 1 := by decide

private theorem m2_cube : ∀ b : Multiplicative (ZMod 2), b * b * b = 1 → b = 1 := by decide

private theorem m3_ne_one : ∀ a : Multiplicative (ZMod 3), a ≠ 1 →
    a = Multiplicative.ofAdd 1 ∨ a = Multiplicative.ofAdd 2 := by
  decide

private theorem m2m2_ne_one : ∀ b c : Multiplicative (ZMod 2), ¬(b = 1 ∧ c = 1) →
    b = Multiplicative.ofAdd 1 ∧ c = 1 ∨ b = 1 ∧ c = Multiplicative.ofAdd 1 ∨
      b = Multiplicative.ofAdd 1 ∧ c = Multiplicative.ofAdd 1 := by
  decide

private theorem z322_prime (d : Z322) (hd : d ≠ 1) (h : d * d = 1 ∨ d * d * d = 1) :
    d = (Multiplicative.ofAdd 1, 1) ∨ d = (Multiplicative.ofAdd 2, 1) ∨
      d = (1, Multiplicative.ofAdd 1, 1) ∨ d = (1, 1, Multiplicative.ofAdd 1) ∨
      d = (1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) := by
  obtain ⟨a, b, c⟩ := d
  rcases h with h | h
  · simp only [Prod.mk_mul_mk, Prod.mk_eq_one] at h
    obtain rfl := m3_sq a h.1
    have hbc : ¬(b = 1 ∧ c = 1) := fun ⟨hb, hc⟩ => hd (by rw [hb, hc]; rfl)
    rcases m2m2_ne_one b c hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · simp only [Prod.mk_mul_mk, Prod.mk_eq_one] at h
    obtain rfl := m2_cube b h.2.1
    obtain rfl := m2_cube c h.2.2
    have ha : a ≠ 1 := fun ha => hd (by rw [ha]; rfl)
    rcases m3_ne_one a ha with rfl | rfl <;> simp

theorem exists_injective_three_two_two {x y z : G} (hxy : Commute x y) (hzx : Commute z x)
    (hzy : Commute z y) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hz : z ^ 3 = 1) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hxy1 : x * y ≠ 1) (hz1 : z ≠ 1) :
    ∃ φ : Multiplicative (ZMod 3 × ZMod 2 × ZMod 2) →* G, Function.Injective φ ∧
      ∀ K : Subgroup G, x ∈ K → y ∈ K → z ∈ K → φ.range ≤ K := by
  let φ₂ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* G :=
    (powHom x 2 hx).noncommCoprod (powHom y 2 hy) fun a b => by
      simp only [powHom_apply]
      exact (hxy.pow_left _).pow_right _
  let φ₃ : Z322 →* G := (powHom z 3 hz).noncommCoprod φ₂ fun a b => by
    simp only [powHom_apply]
    exact (((hzx.pow_right _).mul_right (hzy.pow_right _))).pow_left _
  have hφ : ∀ d : Z322, φ₃ d = z ^ d.1.toAdd.val * (x ^ d.2.1.toAdd.val * y ^ d.2.2.toAdd.val) :=
    fun _ => rfl
  have hD : Nat.card Z322 = 12 := by simp
  have hz2 : z ^ 2 ≠ 1 := by
    intro h
    apply hz1
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz, h]; group
  have hinj : Function.Injective φ₃ := by
    refine injective_of_forall_prime_pow _ fun d hd p hp hpd hdp => ?_
    rw [hD] at hpd
    have h23 : d * d = 1 ∨ d * d * d = 1 := by
      rcases prime_two_or_three hp hpd with rfl | rfl
      · exact Or.inl (by rw [← sq]; exact hdp)
      · exact Or.inr (by rw [← hdp, pow_three, mul_assoc])
    have v1 : (1 : ZMod 3).val = 1 := rfl
    have v2 : (2 : ZMod 3).val = 2 := rfl
    have v1' : (1 : ZMod 2).val = 1 := rfl
    rcases z322_prime d hd h23 with rfl | rfl | rfl | rfl | rfl <;>
      simpa [hφ, v1, v2, v1'] using (by assumption)
  refine ⟨φ₃.comp ((MulEquiv.prodMultiplicative _ _).trans (MulEquiv.prodCongr
    (MulEquiv.refl _) (MulEquiv.prodMultiplicative _ _))).toMonoidHom,
    hinj.comp (MulEquiv.injective _), fun K hxK hyK hzK => ?_⟩
  rintro _ ⟨d, rfl⟩
  rw [MonoidHom.comp_apply, hφ]
  exact K.mul_mem (K.pow_mem hzK _) (K.mul_mem (K.pow_mem hxK _) (K.pow_mem hyK _))

end ThreeTwoTwo

end CFSG.LieType.Multipliers
