module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveComm

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

variable {V : Type} [CommGroup V] [Finite V]

theorem two_pow_five_le_card_commSub_of_frobenius {a b : MulAut V} (ha11 : a ^ 11 = 1)
    (ha1 : a ≠ 1) (hb : b * a * b⁻¹ = a ^ 3) (hV : ∀ v : V, v ^ 2 = 1) :
    2 ^ 5 ≤ Nat.card (commSub b) := by
  set W : Subgroup V := commSub a with hWdef
  have hW10 : 2 ^ 10 ≤ Nat.card W := two_pow_ten_le_card_commSub ha11 ha1 hV
  have hWa : ∀ w ∈ W, a w ∈ W := fun w hw => apply_mem_commSub rfl hw
  have hba : b * a = a ^ 3 * b := by
    calc b * a = b * a * b⁻¹ * b := by group
      _ = a ^ 3 * b := by rw [hb]
  have hWb : ∀ w ∈ W, b w ∈ W := by
    rintro w ⟨v, rfl⟩
    have h : b (a v * v⁻¹) = (a ^ 3) (b v) * (b v)⁻¹ := by
      have : b (a v) = (a ^ 3) (b v) := by
        have := congrArg (fun e : MulAut V => e v) hba
        simpa using this
      rw [map_mul, map_inv, this]
    rw [deltaHom_apply, h]
    exact commSub_pow_le a 3 (deltaHom_mem_commSub (a ^ 3) (b v))
  let C : Subgroup V := W ⊓ fixSub b
  have hC0 : ∀ t ∈ W, b t = t → (a * b * a⁻¹) t = t → t = 1 := by
    intro t htW htb htab
    have hcomm : (a * b * a⁻¹ * b⁻¹) t = t := by
      have hbi : b⁻¹ t = t := by
        have := congrArg (b⁻¹ : MulAut V) htb
        rw [MulAut.inv_apply_self] at this
        exact this.symm
      show (a * b * a⁻¹) (b⁻¹ t) = t
      rw [hbi, htab]
    have he : a * b * a⁻¹ * b⁻¹ = a⁻¹ ^ 2 := by
      calc a * b * a⁻¹ * b⁻¹ = a * (b * a * b⁻¹)⁻¹ := by group
        _ = a * (a ^ 3)⁻¹ := by rw [hb]
        _ = a⁻¹ ^ 2 := by group
    rw [he] at hcomm
    have hfa : t ∈ fixSub (a⁻¹ ^ 2) := hcomm
    have h5 : (a⁻¹ ^ 2) ^ 5 = a := by
      rw [← pow_mul]
      have h1 : a⁻¹ ^ 11 = 1 := by rw [inv_pow, ha11, inv_one]
      calc a⁻¹ ^ (2 * 5) = a * a⁻¹ ^ 11 := by group
        _ = a := by rw [h1, mul_one]
    have hfa' : t ∈ fixSub a := by
      have := fixSub_le_pow (a⁻¹ ^ 2) 5 hfa
      rwa [h5] at this
    have hmem : t ∈ commSub a ⊓ fixSub a := ⟨htW, hfa'⟩
    rw [commSub_inf_fixSub_eq_bot (by decide : Odd 11) ha11 hV, Subgroup.mem_bot] at hmem
    exact hmem
  have hCC : Nat.card C * Nat.card C ≤ Nat.card W := by
    let f : C × C → W := fun p => ⟨(p.1 : V) * a (p.2 : V), Subgroup.mul_mem _
      (p.1.2.1) (hWa _ p.2.2.1)⟩
    have hinj : Function.Injective f := by
      rintro ⟨u, u'⟩ ⟨v, v'⟩ h
      have h' : (u : V) * a (u' : V) = (v : V) * a (v' : V) := congrArg Subtype.val h
      have hu : b (u : V) = u := u.2.2
      have hu' : b (u' : V) = u' := u'.2.2
      have hv : b (v : V) = v := v.2.2
      have hv' : b (v' : V) = v' := v'.2.2
      set t : V := (v : V)⁻¹ * u with ht
      have hr : (v' : V) * (u' : V)⁻¹ ∈ W ∧ b ((v' : V) * (u' : V)⁻¹) = (v' : V) * (u' : V)⁻¹ :=
        ⟨Subgroup.mul_mem _ v'.2.1 (Subgroup.inv_mem _ u'.2.1), by rw [map_mul, map_inv, hv', hu']⟩
      have htaeq : t = a ((v' : V) * (u' : V)⁻¹) := by
        rw [ht, map_mul, map_inv]
        calc (v : V)⁻¹ * u = (v : V)⁻¹ * (u * a u') * (a u')⁻¹ := by group
          _ = (v : V)⁻¹ * (v * a v') * (a u')⁻¹ := by rw [h']
          _ = a v' * (a u')⁻¹ := by group
      have htW : t ∈ W := Subgroup.mul_mem _ (Subgroup.inv_mem _ v.2.1) u.2.1
      have htb : b t = t := by
        rw [ht, map_mul, map_inv, hv, hu]
      have htab : (a * b * a⁻¹) t = t := by
        rw [htaeq]
        show a (b (a⁻¹ (a _))) = a _
        rw [MulAut.inv_apply_self, hr.2]
      have ht1 : t = 1 := hC0 t htW htb htab
      have hvu : (v : V) = u := inv_mul_eq_one.mp ht1
      have hr1 : (v' : V) * (u' : V)⁻¹ = 1 := by
        have h1 : a ((v' : V) * (u' : V)⁻¹) = 1 := by rw [← htaeq]; exact ht1
        exact a.injective (h1.trans (map_one a).symm)
      have hvu' : (v' : V) = u' := mul_inv_eq_one.mp hr1
      exact Prod.ext (Subtype.ext hvu.symm) (Subtype.ext hvu'.symm)
    have := Nat.card_le_card_of_injective f hinj
    rwa [Nat.card_prod] at this
  have hWC : Nat.card W ≤ Nat.card C * Nat.card (commSub b) := by
    let b' : stabAut W := ⟨b, hWb⟩
    have h1 := card_commSub_mul_card_fixSub (restrictHom W b')
    rw [card_fixSub_restrictHom] at h1
    have h2 : Nat.card (commSub (restrictHom W b')) ≤ Nat.card (commSub b) := by
      let g : commSub (restrictHom W b') → commSub b := fun w => ⟨((w : W) : V), by
        obtain ⟨⟨v, hv⟩, hw⟩ := w.2
        have : ((w : W) : V) = b v * v⁻¹ := by rw [← hw]; rfl
        rw [this]
        exact deltaHom_mem_commSub b v⟩
      have hg : Function.Injective g := by
        intro w w' h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h')
      exact Nat.card_le_card_of_injective g hg
    calc Nat.card W = Nat.card (commSub (restrictHom W b')) * Nat.card C := h1.symm
      _ ≤ Nat.card (commSub b) * Nat.card C := Nat.mul_le_mul_right _ h2
      _ = Nat.card C * Nat.card (commSub b) := mul_comm _ _
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hCle : Nat.card C ≤ Nat.card (commSub b) := by
    by_contra hlt
    have hlt' : Nat.card (commSub b) < Nat.card C := Nat.lt_of_not_le hlt
    have : Nat.card W < Nat.card C * Nat.card C :=
      lt_of_le_of_lt hWC (Nat.mul_lt_mul_of_pos_left hlt' hCpos)
    omega
  have hsq : 2 ^ 10 ≤ Nat.card (commSub b) * Nat.card (commSub b) :=
    hW10.trans (hWC.trans (Nat.mul_le_mul_right _ hCle))
  by_contra hlt
  have hlt' : Nat.card (commSub b) ≤ 31 := by omega
  have : Nat.card (commSub b) * Nat.card (commSub b) ≤ 31 * 31 := Nat.mul_le_mul hlt' hlt'
  omega

end CFSG.CGT.PushingUpLit.CGT6M
